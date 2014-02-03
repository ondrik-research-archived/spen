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

typedef struct noll_ta_symbol_t
{
	/// The selectors
	const noll_uid_array* sels;
	/// The string representation (for humans)
	const char* str;
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
bool noll_ta_symbol_match(
	const noll_ta_symbol_t*       lhs,
	const noll_ta_symbol_t*       rhs)
{
	// check that the parameters are sane
	assert(NULL != lhs);
	assert(NULL != rhs);
	assert(NULL != lhs->sels);
	assert(NULL != rhs->sels);

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


void noll_ta_symbol_init()
{
	g_ta_symbols = noll_ta_symbol_array_new();
	noll_ta_symbol_array_reserve(g_ta_symbols, 10);
}


/**
 * @brief  Attempts to find a given in the global database
 *
 * @param[in]  symb  The symbol to be sought
 *
 * @returns  Either a pointer to the unique representation of the symbol @p
 *           symb if it exists, or @p NULL if it does not exist
 */
const noll_ta_symbol_t* noll_ta_symbol_find(
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

const noll_ta_symbol_t* noll_ta_symbol_create(
	const noll_uid_array*            sels)
{
	// check for the input parameters
	assert(NULL != sels);
	assert(NULL != g_ta_symbols);

	noll_ta_symbol_t symb;
	symb.sels = sels;

	const noll_ta_symbol_t* ret_symb;
	if ((ret_symb = noll_ta_symbol_find(&symb)) != NULL)
	{
		return ret_symb;
	}






	NOLL_DEBUG("Inserting new symbol: XXXX\n");

	return NULL;
}
