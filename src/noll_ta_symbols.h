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

#ifndef _NOLL_TA_SYMBOLS_H_
#define _NOLL_TA_SYMBOLS_H_

#ifdef	__cplusplus
extern "C"
{
#endif

#include "noll_types.h"
#include "noll_vector.h"

/* ====================================================================== */
/* Data types */
/* ====================================================================== */

typedef struct noll_ta_symbol noll_ta_symbol_t;

/* ====================================================================== */
/* Functionz */
/* ====================================================================== */


/**
 * @brief  Initializes the database of symbols
 *
 * This function initializes the global database of symbols. This needs to be
 * done before the first call to any @p noll_ta_symbol_* function.
 */
void noll_ta_symbol_init(void);


/**
 * @brief  Destroys the database of symbols
 *
 * Releases allocated memory and does all the housekeeping.
 */
void noll_ta_symbol_destroy(void);


/**
 * @brief  Retrieves the human-readable textual representation of the symbol
 *
 * @param[in]  symb  The input symbol
 *
 * @returns  A human-readable represenation of @p symb
 */
const char* noll_ta_symbol_get_str(
	const noll_ta_symbol_t*       symb);


/**
 * @brief  Creates a unique TA symbol of an allocated node
 *
 * The TA symbols are managed in a global database and the procedure first
 * attempts to find the given symbol in the database and only in the case it is
 * not present there it creates a new record and inserts it into the database.
 *
 * @param[in]  sels     The selectors (note that the order is important)
 * @param[in]  vars     The variables aliased to the node (may be unordered,
 *                      they will be sorted internally)
 * @param[in]  marking  The marking of the node
 *
 * @returns  A unique pointer to the symbol
 */
const noll_ta_symbol_t* noll_ta_symbol_get_unique_allocated(
	const noll_uid_array*            sels,
	const noll_uid_array*            vars,
	const noll_uid_array*            marking);


/**
 * @brief  Creates a unique TA symbol of a node aliased to a variable
 *
 * The TA symbols are managed in a global database and the procedure first
 * attempts to find the given symbol in the database and only in the case it is
 * not present there it creates a new record and inserts it into the database.
 *
 * @param[in]  alias_var  The variable to which the node is aliased
 *
 * @returns  A unique pointer to the symbol
 */
const noll_ta_symbol_t* noll_ta_symbol_get_unique_aliased_var(
	uid_t                            alias_var);


/**
 * @brief  Creates a unique TA symbol of a node aliased using a marking
 *
 * The TA symbols are managed in a global database and the procedure first
 * attempts to find the given symbol in the database and only in the case it is
 * not present there it creates a new record and inserts it into the database.
 *
 * @param[in]  id_rel         ID of the relation
 * @param[in]  alias_marking  The marking to which the node is aliased
 *
 * @returns  A unique pointer to the symbol
 */
const noll_ta_symbol_t* noll_ta_symbol_get_unique_aliased_marking(
	unsigned char                    id_rel,
	const noll_uid_array*            alias_marking);


#ifdef	__cplusplus
}
#endif


#endif /* _NOLL_TA_SYMBOLS_H_ */
