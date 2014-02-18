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

typedef struct noll_tree_node_label
{

} noll_tree_node_label_t;

typedef struct noll_ta_symbol
{
	/// The selectors
	noll_uid_array* sels;

	/// The tree node label of the corresponding node
	noll_tree_node_label_t* tree_node_lb;

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

	char* str = malloc(strlen("NOT IMPLEMENTED") + 1);
	strcpy(str, "NOT IMPLEMENTED");

	return str;
}


void noll_ta_symbol_init()
{
	g_ta_symbols = noll_ta_symbol_array_new();
	noll_ta_symbol_array_reserve(g_ta_symbols, 10);
}


void noll_ta_symbol_destroy()
{
	assert(NULL != g_ta_symbols);

	NOLL_DEBUG(__func__);
	NOLL_DEBUG(": ignoring tree node labels\n");

	for (size_t i = 0; i < noll_vector_size(g_ta_symbols); ++i)
	{
		noll_ta_symbol_t* smb = noll_vector_at(g_ta_symbols, i);
		assert(NULL != smb);
		assert(NULL != smb->sels);
		noll_uid_array_delete(smb->sels);
		free(smb->str);
		free(smb);
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
	assert(NULL != sym->tree_node_lb);
	assert(NULL == sym->str);     // we want the string to be empty

	char* str_node_lb = noll_node_label_to_string(sym->tree_node_lb);
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

	NOLL_DEBUG("WARNING: ");
	NOLL_DEBUG(__func__);
	NOLL_DEBUG(": ignoring tree node labels\n");
}

const noll_ta_symbol_t* noll_ta_symbol_create(
	const noll_uid_array*            sels)
{
	// check for the input parameters
	assert(NULL != sels);
	assert(NULL != g_ta_symbols);

	NOLL_DEBUG(__func__);
	NOLL_DEBUG(": ignoring tree node labels\n");

	noll_ta_symbol_t symb;

	// this issues a warning because of the -Wcast-qual flag of GCC
	symb.sels = (noll_uid_array*)sels;

	const noll_ta_symbol_t* ret_symb;
	if ((ret_symb = noll_ta_symbol_find(&symb)) != NULL)
	{
		return ret_symb;
	}

	noll_ta_symbol_t* alloc_symb = malloc(sizeof(*alloc_symb));
	assert(NULL != alloc_symb);
	alloc_symb->str = NULL;                       // clear the string
	noll_uid_array* alloc_sels = noll_uid_array_new();
	assert(NULL != alloc_sels);
	noll_uid_array_copy(alloc_sels, sels);        // copy selectors
	alloc_symb->sels = alloc_sels;

	noll_ta_symbol_fill_str(alloc_symb);          // compute the string
	assert(NULL != alloc_symb->str);

	NOLL_DEBUG("Inserting new symbol: %s\n", alloc_symb->str);

	noll_ta_symbol_array_push(g_ta_symbols, alloc_symb);

	return alloc_symb;
}
