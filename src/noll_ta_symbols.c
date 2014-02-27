/**************************************************************************/
/*                                                                        */
/*  NOLL decision procedure                                               */
/*                                                                        */
/*  Copyright (C) 2013                                                    */
/*    LIAFA (University of Paris Diderot and CNRS)                        */
/*    VeriFIT (Brno University of Technology)                             */
/*                                                                        */
/*                                                                        */
/*  you can redistribute it and/or modify it under the terms of the GNU   */
/*  Lesser General Public License as published by the Free Software       */
/*  Foundation, version 3.                                                */
/*                                                                        */
/*  It is distributed in the hope that it will be useful,                 */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of        */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         */
/*  GNU Lesser General Public License for more details.                   */
/*                                                                        */
/*  See the GNU Lesser General Public License version 3.                  */
/*  for more details (enclosed in the file LICENSE).                      */
/*                                                                        */
/**************************************************************************/

#include "noll.h"
#include "noll_ta_symbols.h"

/* ====================================================================== */
/* Data typez */
/* ====================================================================== */

/// Enumeration of possible aliasing of nodes
enum noll_tree_label_type_t
{
	NOLL_TREE_LABEL_ALLOCATED,        ///< the node is allocated: no aliasing is used
	NOLL_TREE_LABEL_ALIASING_VARIABLE,///< a node with a program variable is aliased
	NOLL_TREE_LABEL_ALIASING_MARKING, ///< marking is used as the relation
};

typedef struct noll_ta_symbol
{
	/// The type of the label (see enum @p noll_tree_label_type_t)
	unsigned char label_type;

	union {
		/// The structure used for allocated nodes (for label_type ==
		/// NOLL_TREE_LABEL_ALLOCATED)
		struct
		{
			/// The selectors
			noll_uid_array* sels;

			/// Variables that might alias with the node
			noll_uid_array* vars;

			/// The (least) marking of the node
			noll_uid_array* marking;
		} allocated;

		/// Marking of the aliased node (for label_type ==
		/// NOLL_TREE_LABEL_ALIASING_MARKING)
		struct
		{
			/// The marking
			noll_uid_array* marking;

			/// Identifier of the relation
			unsigned char id_relation;
		} alias_marking;

		/// Name of the variable the node is aliased to (for aliasing_type ==
		/// NOLL_TREE_LABEL_ALIASING_VARIABLE)
		uid_t alias_var;
	};

	/// The string representation (for humans)
	char* str;
} noll_ta_symbol_t;

// a database of symbols
NOLL_VECTOR_DECLARE( noll_ta_symbol_array , noll_ta_symbol_t* )
NOLL_VECTOR_DEFINE( noll_ta_symbol_array , noll_ta_symbol_t* )

/* ====================================================================== */
/* Globalz */
/* ====================================================================== */

/// The global database of symbols
/// @todo: it would be more efficient to have 3 databases for every label_type
static noll_ta_symbol_array* g_ta_symbols;

/* ====================================================================== */
/* Functionz */
/* ====================================================================== */


/**
 * @brief  Gets a string for an UID array
 *
 * @param[in]  arr   The UID array
 *
 * @returns  A string representing @p arr. It is a responsibility of the caller
 *           to dispose of the returned memory.
 */
static char* noll_uid_array_tostring(
	const noll_uid_array*    arr)
{
	assert(NULL != arr);
	static const size_t BUFFER_SIZE = 128;

	char* buffer = malloc(BUFFER_SIZE);
	size_t index = 0;
	assert(index < BUFFER_SIZE);

	for (size_t i = 0; i < noll_vector_size(arr); ++i)
	{
		assert(index < BUFFER_SIZE);
		index += snprintf(
			&buffer[index],
			BUFFER_SIZE - index,
			"%d, ",
			noll_vector_at(arr, i));
	}

	if (noll_vector_size(arr) > 0)
	{
		index -= 2;   // move at the position of the last ','
	}

	assert(index < BUFFER_SIZE);
	buffer[index] = '\0';

	return buffer;
}


/**
 * @brief  Checks whether two symbols match
 *
 * @param[in]  lhs  The left-hand side
 * @param[in]  rhs  The right-hand side
 *
 * @returns  @p true if @p lhs and @p rhs match, @p false otherwise
 */
static bool noll_ta_symbol_match(
	const noll_ta_symbol_t*       lhs,
	const noll_ta_symbol_t*       rhs)
{
	// check that the parameters are sane
	assert(NULL != lhs);
	assert(NULL != rhs);

	if (lhs->label_type != rhs->label_type)
	{	// if the types do not match
		return false;
	}

	switch (lhs->label_type)
	{
		case NOLL_TREE_LABEL_ALLOCATED:
		{
			assert(NULL != lhs->allocated.sels);
			assert(NULL != rhs->allocated.sels);
			if (!noll_uid_array_equal(lhs->allocated.sels, rhs->allocated.sels))
			{
				return false;
			}

			assert(NULL != lhs->allocated.vars);
			assert(NULL != rhs->allocated.vars);
			if (!noll_uid_array_equal(lhs->allocated.vars, rhs->allocated.vars))
			{
				return false;
			}

			assert(NULL != lhs->allocated.marking);
			assert(NULL != rhs->allocated.marking);
			if (!noll_uid_array_equal(lhs->allocated.marking, rhs->allocated.marking))
			{
				return false;
			}

			return true;
		}

		case NOLL_TREE_LABEL_ALIASING_VARIABLE:
		{
			return lhs->alias_var == rhs->alias_var;
		}

		case NOLL_TREE_LABEL_ALIASING_MARKING:
		{
			if (lhs->alias_marking.id_relation != rhs->alias_marking.id_relation)
			{
				return false;
			}

			return noll_uid_array_equal(
				lhs->alias_marking.marking, rhs->alias_marking.marking);
		}

		default:
		{
			assert(false);
		}
	}
}


const char* noll_ta_symbol_get_str(
	const noll_ta_symbol_t*       symb)
{
	// check inputs
	assert(NULL != symb);
	assert(NULL != symb->str);

	return symb->str;
}


/**
 * @brief  Generates a string for a selectors
 *
 * This function generates a human-readable string for a textual representation
 * of a vector of selectors. The function returns a non-shared dynamically
 * allocated memory block---it is the responsibility of the caller to dispose
 * of it.
 *
 * @param[in]  sels  The selectors from which the symbol is to be composed
 *
 * @returns  Pointer to a dynamically allocated memory block with the
 *           human-readable representation of the selectors. After the return,
 *           the caller is responsible for deallocating this block.
 */
static char* noll_sels_to_string_symbol(
	const noll_uid_array*           sels)
{
	assert(NULL != sels);

	// compute the necessary memory for the string
	size_t str_len = 1;                          // for '\0'
	str_len += (noll_vector_size(sels)-1) * 2;   // for (n-1) * ", "
	for (size_t i = 0; i < noll_vector_size(sels); ++i)
	{
		const char* field_name = noll_field_name(noll_vector_at(sels, i));
		assert(NULL != field_name);
		NOLL_DEBUG("Processing field %u with the name %s\n", noll_vector_at(sels, i), field_name);

		str_len += strlen(field_name);
	}

	char* str_symbol = malloc(str_len);
	assert(NULL != str_symbol);


	size_t cnt = 0;      // where to start copying
	for (size_t i = 0; i < noll_vector_size(sels); ++i)
	{
		if (0 != cnt)
		{	// if we are not at the beginning
			str_symbol[cnt++] = ',';
			str_symbol[cnt++] = ' ';
		}

		const char* field_name = noll_field_name(noll_vector_at(sels, i));
		strcpy(&str_symbol[cnt], field_name);
		cnt += strlen(field_name);
	}

	// check that everything is correct
	assert(cnt == str_len - 1);

	str_symbol[str_len-1] = '\0';

	return str_symbol;
}


void noll_ta_symbol_init()
{
	g_ta_symbols = noll_ta_symbol_array_new();
	noll_ta_symbol_array_reserve(g_ta_symbols, 10);
}


/**
 * @brief  A function to safely deallocate a TA symbol
 *
 * This function releases the memory allocated by a TA symbol. After the call
 * to the function, @p sym is invalid and the memory deallocated.
 *
 * @param[in,out]  sym  The symbol to be killed
 */
static void noll_ta_symbol_kill(
	noll_ta_symbol_t*       sym)
{
	assert(NULL != sym);

	switch (sym->label_type)
	{
		case NOLL_TREE_LABEL_ALLOCATED:
		{
			assert(NULL != sym->allocated.sels);
			noll_uid_array_delete(sym->allocated.sels);
			assert(NULL != sym->allocated.marking);
			noll_uid_array_delete(sym->allocated.marking);
			assert(NULL != sym->allocated.vars);
			noll_uid_array_delete(sym->allocated.vars);

			break;
		}

		case NOLL_TREE_LABEL_ALIASING_VARIABLE:
		{
			// nothing spectacular
			break;
		}

		case NOLL_TREE_LABEL_ALIASING_MARKING:
		{
			assert(NULL != sym->alias_marking.marking);
			noll_uid_array_delete(sym->alias_marking.marking);

			break;
		}

		default:
		{
			assert(false);
		}
	}

	if (NULL != sym->str)
	{	// the string may not be allocated
		free(sym->str);
	}

	free(sym);
}


void noll_ta_symbol_destroy()
{
	assert(NULL != g_ta_symbols);

	for (size_t i = 0; i < noll_vector_size(g_ta_symbols); ++i)
	{
		noll_ta_symbol_t* smb = noll_vector_at(g_ta_symbols, i);
		assert(NULL != smb);
		noll_ta_symbol_kill(smb);
	}

	noll_ta_symbol_array_delete(g_ta_symbols);
}


/**
 * @brief  Attempts to find a given symbol in the global database
 *
 * @param[in]  symb  The symbol to be sought
 *
 * @returns  Either a pointer to the unique representation of the symbol @p
 *           symb if it exists, or @p NULL if it does not exist
 */
static const noll_ta_symbol_t* noll_ta_symbol_find(
	const noll_ta_symbol_t*           symb)
{
	assert(NULL != symb);
	assert(NULL != g_ta_symbols);

	for (size_t i = 0; i < noll_vector_size(g_ta_symbols); ++i)
	{
		const noll_ta_symbol_t* iter = noll_vector_at(g_ta_symbols, i);
		if (noll_ta_symbol_match(symb, iter))
		{
			return iter;
		}
	}

	return NULL;
}


/**
 * @brief  Retrieves the string for an allocated node
 *
 * @param[in]  sym  The node the string of which is desired
 *
 * @returns  The string representation of the symbol. The caller is responsible
 *           for the deallocation of the returned memory.
 */
static char* noll_ta_symbol_alloc_str(
	const noll_ta_symbol_t* sym)
{
	assert(NULL != sym);
	assert(NOLL_TREE_LABEL_ALLOCATED == sym->label_type);
	assert(NULL != sym->allocated.sels);
	assert(NULL != sym->allocated.marking);
	assert(NULL != sym->allocated.vars);

	char* str_sels = noll_sels_to_string_symbol(sym->allocated.sels);
	assert(NULL != str_sels);
	char* str_mark = noll_uid_array_tostring(sym->allocated.marking);
	assert(NULL != str_mark);
	char* str_vars = noll_uid_array_tostring(sym->allocated.vars);
	assert(NULL != str_vars);

	// TODO: the following might not have to be done if we return the length of
	// the strings from the respective function calls
	size_t len_sels = strlen(str_sels);
	size_t len_mark = strlen(str_mark);
	size_t len_vars = strlen(str_vars);

	size_t total_len =
		1 /* '[' */ +
		1 /* '<' */ +
		len_sels +
		1 /* '>' */ +
		1 /* ',' */ +
		1 /* ' ' */ +
		1 /* '[' */ +
		len_mark +
		1 /* ']' */ +
		1 /* ',' */ +
		1 /* ' ' */ +
		1 /* '{' */ +
		len_vars +
		1 /* '}' */ +
		1 /* ']' */ +
		1 /* '\0' */;

	char* str = malloc(total_len);
	size_t index = 0;
	str[index++] = '[';
	str[index++] = '<';
	strcpy(&str[index], str_sels);
	index += len_sels;
	str[index++] = '>';
	str[index++] = ',';
	str[index++] = ' ';
	str[index++] = '[';
	strcpy(&str[index], str_mark);
	index += len_mark;
	str[index++] = ']';
	str[index++] = ',';
	str[index++] = ' ';
	str[index++] = '{';
	strcpy(&str[index], str_vars);
	index += len_vars;
	str[index++] = '}';
	str[index++] = ']';
	assert(index == total_len - 1);
	str[index] = '\0';

	// remove the temporary strings
	free(str_sels);
	free(str_mark);
	free(str_vars);

	return str;
}


/**
 * @brief  Retrieves the string for a node aliasing to a variable
 *
 * @param[in]  sym  The node the string of which is desired
 *
 * @returns  The string representation of the symbol. The caller is responsible
 *           for the deallocation of the returned memory.
 */
static char* noll_ta_symbol_alias_var_str(
	const noll_ta_symbol_t* sym)
{
	assert(NULL != sym);
	assert(NOLL_TREE_LABEL_ALIASING_VARIABLE == sym->label_type);

	assert(false);
}


/**
 * @brief  Retrieves the string for a node aliasing to a marking
 *
 * @param[in]  sym  The node the string of which is desired
 *
 * @returns  The string representation of the symbol. The caller is responsible
 *           for the deallocation of the returned memory.
 */
static char* noll_ta_symbol_alias_marking_str(
	const noll_ta_symbol_t* sym)
{
	assert(NULL != sym);
	assert(NOLL_TREE_LABEL_ALIASING_MARKING == sym->label_type);
	assert(NULL != sym->alias_marking.marking);

	char* str_mark = noll_uid_array_tostring(sym->alias_marking.marking);
	assert(NULL != str_mark);
	size_t len_mark = strlen(str_mark);

	size_t total_len =
		1 /* '[' */ +
		1 /* 's' */ +
		1 /* 'X' */ +
		1 /* '(' */ +
		1 /* '[' */ +
		len_mark +
		1 /* ']' */ +
		1 /* ')' */ +
		1 /* ']' */ +
		1 /* '\0' */;

	char* str = malloc(total_len);
	size_t index = 0;
	str[index++] = '[';
	str[index++] = 's';

	switch (sym->alias_marking.id_relation)
	{
		case 1:
		{
			str[index++] = '1';
			break;
		}

		case 2:
		{
			str[index++] = '2';
			break;
		}

		case 3:
		{
			str[index++] = '3';
			break;
		}

		case 4:
		{
			str[index++] = '4';
			break;
		}

		default:
		{
			assert(false);
		}
	}

	str[index++] = '(';
	str[index++] = '[';
	strcpy(&str[index], str_mark);
	index += len_mark;
	str[index++] = ']';
	str[index++] = ')';
	str[index++] = ']';
	str[index++] = '\0';
	assert(total_len == index);

	free(str_mark);

	return str;
}


/**
 * @brief  Fills the string representation for a symbol
 *
 * This function fills in the string representation data field of a symbol
 * according to the stored data.
 *
 * @param[in,out]  sym  The symbol to be modified
 */
static void noll_ta_symbol_fill_str(
	noll_ta_symbol_t*            sym)
{
	assert(NULL != sym);

	switch (sym->label_type)
	{
		case NOLL_TREE_LABEL_ALLOCATED:
		{
			sym->str = noll_ta_symbol_alloc_str(sym);
			break;
		}

		case NOLL_TREE_LABEL_ALIASING_VARIABLE:
		{
			sym->str = noll_ta_symbol_alias_var_str(sym);
			break;
		}

		case NOLL_TREE_LABEL_ALIASING_MARKING:
		{
			sym->str = noll_ta_symbol_alias_marking_str(sym);
			break;
		}

		default:
		{
			assert(false);
		}
	}
}


/**
 * @brief  Allocates and pre-fills a TA symbol
 *
 * This function allocates a new TA symbol and pre-fills its data it is the
 * responsibility of the caller to deallocate the returned symbol.
 *
 * @returns  An allocated TA symbol. It is the responsibility of the caller to
 * deallocate it.
 */
static noll_ta_symbol_t* noll_ta_symbol_create(void)
{
	noll_ta_symbol_t* alloc_symb = calloc(1, sizeof(*alloc_symb));
	assert(NULL != alloc_symb);

	return alloc_symb;
}


/**
 * @brief  Spawns a symbol by either finding in a DB or adding and returning
 *
 * This function, given the symbol @p symb, attempts to find @p symb in the
 * global database of symbols and if it is found, @p symb is deleted and the
 * found instance is returned, if not, then @p symb is added to the global
 * database and pointer to the instance is returned.
 *
 * @param[in]  symb  The symbol to be spawned
 *
 * @returns  The spawned symbol
 */
static const noll_ta_symbol_t* noll_symbol_spawn(
	noll_ta_symbol_t*            symb)
{
	assert(NULL != symb);

	const noll_ta_symbol_t* ret_symb;
	if ((ret_symb = noll_ta_symbol_find(symb)) != NULL)
	{
		noll_ta_symbol_kill(symb);
		return ret_symb;
	}

	noll_ta_symbol_fill_str(symb);          // compute the string
	assert(NULL != symb->str);

	NOLL_DEBUG("Inserting new symbol: %s\n", symb->str);

	noll_ta_symbol_array_push(g_ta_symbols, symb);

	return symb;
}


const noll_ta_symbol_t* noll_ta_symbol_get_unique_allocated(
	const noll_uid_array*            sels,
	const noll_uid_array*            vars,
	const noll_uid_array*            marking)
{
	// check for the input parameters
	assert(NULL != sels);
	assert(NULL != vars);
	assert(NULL != marking);

	noll_ta_symbol_t* symb = noll_ta_symbol_create();
	assert(NULL != symb);

	symb->str = NULL;                       // clear the string
	symb->label_type = NOLL_TREE_LABEL_ALLOCATED;
	noll_uid_array* alloc_sels = noll_uid_array_new();
	assert(NULL != alloc_sels);
	noll_uid_array_copy(alloc_sels, sels);        // copy selectors
	symb->allocated.sels = alloc_sels;

	NOLL_DEBUG("WARNING: ");
	NOLL_DEBUG(__func__);
	NOLL_DEBUG(": Not sorting the variables!!!!!\n");

	symb->allocated.vars = noll_uid_array_new();
	assert(NULL != symb->allocated.vars);
	symb->allocated.marking = noll_uid_array_new();
	assert(NULL != symb->allocated.marking);
	// implicit is no aliasing

	// get the unique representation of the symbol
	const noll_ta_symbol_t* ret_sym = noll_symbol_spawn(symb);
	assert(NULL != ret_sym);

	return ret_sym;
}


const noll_ta_symbol_t* noll_ta_symbol_get_unique_aliased_var(
	uid_t                            alias_var)
{
	noll_ta_symbol_t* symb = noll_ta_symbol_create();
	assert(NULL != symb);

	symb->label_type = NOLL_TREE_LABEL_ALIASING_VARIABLE;
	symb->alias_var = alias_var;

	// get the unique representation of the symbol
	const noll_ta_symbol_t* ret_sym = noll_symbol_spawn(symb);
	assert(NULL != ret_sym);
	return ret_sym;
}


const noll_ta_symbol_t* noll_ta_symbol_get_unique_aliased_marking(
	unsigned char                    id_rel,
	const noll_uid_array*            alias_marking)
{
	// check for the input parameters
	assert(NULL != alias_marking);
	assert(0 < id_rel);
	assert(5 > id_rel);

	noll_ta_symbol_t* symb = noll_ta_symbol_create();
	assert(NULL != symb);
	symb->label_type = NOLL_TREE_LABEL_ALIASING_MARKING;
	symb->alias_marking.marking = noll_uid_array_new();
	assert(NULL != symb->alias_marking.marking);
	noll_uid_array_copy(symb->alias_marking.marking, alias_marking);
	symb->alias_marking.id_relation = id_rel;

	// get the unique representation of the symbol
	const noll_ta_symbol_t* ret_sym = noll_symbol_spawn(symb);
	assert(NULL != ret_sym);
	return ret_sym;
}
