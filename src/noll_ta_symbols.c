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
enum
{
	NOLL_TREE_LABEL_ALIASING_NO,      ///< no aliasing is used
	NOLL_TREE_LABEL_ALIASING_VARIABLE,///< a node with a program variable is aliased
	NOLL_TREE_LABEL_ALIASING_MARKING, ///< marking is used as the relation
};

typedef struct noll_tree_node_label
{
	/// Variables that might alias with the node
	noll_uid_array* vars;

	/// The (least) marking of the node
	noll_uid_array* marking;

	/// The type of aliasing used
	unsigned char aliasing_type;

	union {
		/// Marking of the aliased node (for aliasing type ==
		/// NOLL_TREE_LABEL_ALIASING_MARKING)
		/// TODO: would it be possible to store this in 'marking'? We might not
		/// need both valid...
		noll_uid_array* alias_marking;

		/// Name of the variable the node is aliased to (for aliasing_type ==
		/// NOLL_TREE_LABEL_ALIASING_VARIABLE)
		uid_t alias_var;
	};
} noll_tree_node_label_t;

typedef struct noll_ta_symbol
{
	/// The selectors
	noll_uid_array* sels;

	/// The tree node label of the corresponding node
	noll_tree_node_label_t tree_node_lb;

	/// The string representation (for humans)
	char* str;
} noll_ta_symbol_t;

// a database of symbols
NOLL_VECTOR_DECLARE( noll_ta_symbol_array , noll_ta_symbol_t* )
NOLL_VECTOR_DEFINE( noll_ta_symbol_array , noll_ta_symbol_t* )

/* ====================================================================== */
/* Globalz */
/* ====================================================================== */

static noll_ta_symbol_array* g_ta_symbols;

/* ====================================================================== */
/* Functionz */
/* ====================================================================== */


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
	assert(NULL != lhs->sels);
	assert(NULL != rhs->sels);

	NOLL_DEBUG(__func__);
	NOLL_DEBUG(": ignoring tree node labels\n");

	if (noll_vector_size(lhs->sels) != noll_vector_size(rhs->sels))
	{
		return false;
	}

	// the order of the selectors needs to match
	for (size_t i = 0; i < noll_vector_size(lhs->sels); ++i)
	{
		if (noll_vector_at(lhs->sels, i) != noll_vector_at(rhs->sels, i))
		{
			return false;
		}
	}

	return true;
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
	// check that the caller is not mischievous
	assert(NULL != sels);

	// compute the necessary memory for the string
	size_t str_len = 3;                          // for '<', '>', and '\0'
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


	str_symbol[0] = '<';
	size_t cnt = 1;      // where to start copying
	for (size_t i = 0; i < noll_vector_size(sels); ++i)
	{
		if (1 != cnt)
		{	// if we are not at the beginning
			str_symbol[cnt++] = ',';
			str_symbol[cnt++] = ' ';
		}

		const char* field_name = noll_field_name(noll_vector_at(sels, i));
		strcpy(&str_symbol[cnt], field_name);
		cnt += strlen(field_name);
	}

	// check that everything is correct
	assert(cnt == str_len - 2);

	str_symbol[str_len-2] = '>';
	str_symbol[str_len-1] = '\0';

	return str_symbol;
}


/**
 * @brief  Generates a string for a tree node label
 *
 * This functions generates a human-readable string for a textual
 * representation of a tree node label. The function returns a non-shared
 * dynamically allocated memory block---it is the responsibility of the caller
 * to dispose of it.
 *
 * @param[in]  node_lb  The tree node label
 *
 * @returns  Pointer to a dynamically allocated memory block with the
 *           human-readable representation of the tree node label. After the
 *           return, the caller is responsible for deallocating this block.
 */
static char* noll_node_label_to_string(
	const noll_tree_node_label_t*     node_lb)
{
	assert(NULL != node_lb);

	static const size_t BUFFER_SIZE = 1024;

	char* buffer = malloc(BUFFER_SIZE);
	size_t index = 0;
	assert(index < BUFFER_SIZE);
	buffer[index++] = '{';

	// first, let's print the variables
	const noll_uid_array* vars = node_lb->vars;
	assert(NULL != vars);
	for (size_t i = 0; i < noll_vector_size(vars); ++i)
	{
		assert(index < BUFFER_SIZE);
		index += snprintf(
			&buffer[index],
			BUFFER_SIZE - index,
			"%u, ",
			noll_vector_at(vars, i));
	}

	if (noll_vector_size(vars) > 0)
	{
		index -= 2;   // move at the position of the last ','
	}

	assert(index < BUFFER_SIZE);
	buffer[index++] = '}';
	assert(index < BUFFER_SIZE);
	buffer[index++] = ',';
	assert(index < BUFFER_SIZE);
	buffer[index++] = ' ';

	// second, let's print the marking
	const noll_uid_array* marking = node_lb->marking;
	assert(NULL != marking);
	assert(index < BUFFER_SIZE);
	buffer[index++] = '[';
	for (size_t i = 0; i < noll_vector_size(marking); ++i)
	{
		assert(index < BUFFER_SIZE);
		index += snprintf(
			&buffer[index],
			BUFFER_SIZE - index,
			"%d, ",
			noll_vector_at(marking, i));
	}

	if (noll_vector_size(marking) > 0)
	{
		index -= 2;   // move at the position of the last ','
	}

	assert(index < BUFFER_SIZE);
	buffer[index++] = ']';
	assert(index < BUFFER_SIZE);
	buffer[index++] = ',';
	assert(index < BUFFER_SIZE);
	buffer[index++] = ' ';

	switch (node_lb->aliasing_type)
	{
		case NOLL_TREE_LABEL_ALIASING_NO:
		{
			assert(index < BUFFER_SIZE);
			buffer[index++] = '_';
			assert(index < BUFFER_SIZE);
			buffer[index++] = '|';
			assert(index < BUFFER_SIZE);
			buffer[index++] = '_';

			break;
		}

		case NOLL_TREE_LABEL_ALIASING_VARIABLE:
		{
			assert(index < BUFFER_SIZE);
			buffer[index++] = 's';
			assert(index < BUFFER_SIZE);
			buffer[index++] = '0';
			assert(index < BUFFER_SIZE);
			buffer[index++] = '(';

			assert(index < BUFFER_SIZE);
			index += snprintf(
				&buffer[index],
				BUFFER_SIZE - index,
				"%u, ",
				node_lb->alias_var);

			assert(index < BUFFER_SIZE);
			buffer[index++] = ')';

			break;
		}

		case NOLL_TREE_LABEL_ALIASING_MARKING:
		{
			assert(index < BUFFER_SIZE);
			buffer[index++] = 's';
			assert(index < BUFFER_SIZE);
			buffer[index++] = '(';
			assert(index < BUFFER_SIZE);
			buffer[index++] = '[';

			const noll_uid_array* marking = node_lb->alias_marking;
			assert(NULL != marking);
			assert(index < BUFFER_SIZE);
			buffer[index++] = '[';
			for (size_t i = 0; i < noll_vector_size(marking); ++i)
			{
				assert(index < BUFFER_SIZE);
				index += snprintf(
					&buffer[index],
					BUFFER_SIZE - index,
					"%d, ",
					noll_vector_at(marking, i));
			}

			if (noll_vector_size(marking) > 0)
			{
				index -= 2;   // move at the position of the last ','
			}

			assert(index < BUFFER_SIZE);
			buffer[index++] = ']';
			assert(index < BUFFER_SIZE);
			buffer[index++] = ')';

			break;
		}

		default:
		{
			NOLL_DEBUG("ERROR: Invalid value of node_lb->aliasing_type\n");
			assert(false);
		}
	}

	// just to make sure the string is always NULL-terminated
	buffer[BUFFER_SIZE-1] = '\0';
	return buffer;
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

	assert(NULL != sym->sels);
	noll_uid_array_delete(sym->sels);
	if (NULL != sym->str)
	{	// the string may not be allocated
		free(sym->str);
	}

	assert(NULL != sym->tree_node_lb.vars);
	noll_uid_array_delete(sym->tree_node_lb.vars);
	assert(NULL != sym->tree_node_lb.marking);
	noll_uid_array_delete(sym->tree_node_lb.marking);

	switch (sym->tree_node_lb.aliasing_type)
	{
		case NOLL_TREE_LABEL_ALIASING_NO:
		case NOLL_TREE_LABEL_ALIASING_VARIABLE:
		{
			// no reason to handle
			break;
		}

		case NOLL_TREE_LABEL_ALIASING_MARKING:
		{
			assert(NULL != sym->tree_node_lb.alias_marking);
			noll_uid_array_delete(sym->tree_node_lb.alias_marking);

			break;
		}

		default:
		{
			NOLL_DEBUG("Invalid value of aliasing type\n");
			assert(false);

			break;
		}
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
 * @brief  Fills the string representation for a symbol
 *
 * This function fills in the string representation data field of a symbol
 * according to the stored selectors and node labels.
 *
 * @param[in,out]  sym  The symbol to be modified
 */
static void noll_ta_symbol_fill_str(
	noll_ta_symbol_t*            sym)
{
	assert(NULL != sym);
	assert(NULL != sym->sels);
	assert(NULL == sym->str);     // we want the string to be empty

	char* str_node_lb = noll_node_label_to_string(&sym->tree_node_lb);
	char* str_sels = noll_sels_to_string_symbol(sym->sels);

	// TODO: the following might not have to be done if we return the length of
	// the strings from the respective function calls
	size_t len_node_lb = strlen(str_node_lb);
	size_t len_sels = strlen(str_sels);
	size_t total_len =
		1 /* '[' */ +
		1 /* '(' */ +
		len_node_lb +
		1 /* ')' */ +
		1 /* ':' */ +
		1 /* ' ' */ +
		len_sels +
		1 /* ']' */ +
		1 /* '\0' */;

	sym->str = malloc(total_len);
	size_t index = 0;
	sym->str[index++] = '[';
	sym->str[index++] = '(';
	strcpy(&sym->str[index], str_node_lb);
	index += len_node_lb;
	sym->str[index++] = ')';
	sym->str[index++] = ':';
	sym->str[index++] = ' ';
	strcpy(&sym->str[index], str_sels);
	index += len_sels;
	sym->str[index++] = ']';
	assert(index == total_len - 1);
	sym->str[index] = '\0';

	// remove the temporary strings
	free(str_node_lb);
	free(str_sels);

	NOLL_DEBUG("WARNING: ");
	NOLL_DEBUG(__func__);
	NOLL_DEBUG(": ignoring tree node labels\n");
}


static void noll_ta_symbol_fill_non_aliased(
	noll_ta_symbol_t*                sym,
	const noll_uid_array*            sels,
	const noll_uid_array*            vars,
	const noll_uid_array*            marking)
{
	assert(NULL != sym);
	assert(NULL != sels);
	assert(NULL != vars);
	assert(NULL != marking);

	sym->tree_node_lb.aliasing_type = NOLL_TREE_LABEL_ALIASING_NO;

	sym->str = NULL;                       // clear the string
	noll_uid_array* alloc_sels = noll_uid_array_new();
	assert(NULL != alloc_sels);
	noll_uid_array_copy(alloc_sels, sels);        // copy selectors
	sym->sels = alloc_sels;

	sym->tree_node_lb.vars = noll_uid_array_new();
	assert(NULL != sym->tree_node_lb.vars);
	sym->tree_node_lb.marking = noll_uid_array_new();
	assert(NULL != sym->tree_node_lb.marking);
	// implicit is no aliasing
	sym->tree_node_lb.aliasing_type = NOLL_TREE_LABEL_ALIASING_NO;

	NOLL_DEBUG("WARNING: Creating fake tree node label\n");

	noll_uid_array_push(sym->tree_node_lb.vars, 1);
	noll_uid_array_push(sym->tree_node_lb.vars, 2);
	noll_uid_array_push(sym->tree_node_lb.vars, 3);

	noll_uid_array_push(sym->tree_node_lb.marking, -1);
	noll_uid_array_push(sym->tree_node_lb.marking, 1);
	noll_uid_array_push(sym->tree_node_lb.marking, 2);
	noll_uid_array_push(sym->tree_node_lb.marking, 3);
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


const noll_ta_symbol_t* noll_ta_symbol_get_unique_non_aliased(
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
	noll_ta_symbol_fill_non_aliased(symb, sels, vars, marking);

	// get the unique representation of the symbol
	const noll_ta_symbol_t* ret_sym = noll_symbol_spawn(symb);
	assert(NULL != ret_sym);
	return ret_sym;
}


const noll_ta_symbol_t* noll_ta_symbol_get_unique_aliased_var(
	const noll_uid_array*            sels,
	const noll_uid_array*            vars,
	const noll_uid_array*            marking,
	uid_t                            alias_var)
{
	// check for the input parameters
	assert(NULL != sels);
	assert(NULL != vars);
	assert(NULL != marking);

	noll_ta_symbol_t* symb = noll_ta_symbol_create();
	assert(NULL != symb);
	noll_ta_symbol_fill_non_aliased(symb, sels, vars, marking);
	symb->tree_node_lb.aliasing_type = NOLL_TREE_LABEL_ALIASING_VARIABLE;
	symb->tree_node_lb.alias_var = alias_var;

	// get the unique representation of the symbol
	const noll_ta_symbol_t* ret_sym = noll_symbol_spawn(symb);
	assert(NULL != ret_sym);
	return ret_sym;
}


const noll_ta_symbol_t* noll_ta_symbol_get_unique_aliased_marking(
	const noll_uid_array*            sels,
	const noll_uid_array*            vars,
	const noll_uid_array*            marking,
	const noll_uid_array*            alias_marking)
{
	// check for the input parameters
	assert(NULL != sels);
	assert(NULL != vars);
	assert(NULL != marking);

	noll_ta_symbol_t* symb = noll_ta_symbol_create();
	assert(NULL != symb);
	noll_ta_symbol_fill_non_aliased(symb, sels, vars, marking);
	symb->tree_node_lb.aliasing_type = NOLL_TREE_LABEL_ALIASING_MARKING;
	symb->tree_node_lb.alias_marking = noll_uid_array_new();
	assert(NULL != symb->tree_node_lb.alias_marking);
	noll_uid_array_copy(symb->tree_node_lb.alias_marking, alias_marking);

	// get the unique representation of the symbol
	const noll_ta_symbol_t* ret_sym = noll_symbol_spawn(symb);
	assert(NULL != ret_sym);
	return ret_sym;
}
