/**************************************************************************/
/*                                                                        */
/*  NOLL decision procedure                                               */
/*                                                                        */
/*  Copyright (C) 2012-2014                                               */
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

/**
 * Interface to libvata.
 */

#ifndef LIBVATA_NOLL_IFACE_H_
#define LIBVATA_NOLL_IFACE_H_

#include <stdlib.h>


#ifdef __cplusplus
	extern "C" {
#endif

/* ====================================================================== */
/* Datatypes */
/* ====================================================================== */
struct type_noll_ta_t;

typedef struct type_noll_ta_t vata_ta_t;

typedef vata_ta_t noll_ta_t;

typedef size_t vata_state_t;
typedef void vata_symbol_t;

/* ====================================================================== */
/* Functions */
/* ====================================================================== */

/**
 * @brief  Creates an empty TA
 *
 * This function creates an empty tree automaton (TA) on the heap and returns a
 * pointer to it. The tree automaton needs to be freed using the vata_free_ta()
 * function to avoid resource leakage.
 *
 * @returns  Pointer to the created TA
 */
vata_ta_t* vata_create_ta(void);


/**
 * @brief  Frees a TA
 *
 * This function returns resources associated with an allocated TA to the
 * system.
 *
 * @param[in]  ta  The TA to be freed, if NULL, nothing happens.
 */
void vata_free_ta(
	vata_ta_t*          ta);


/**
 * @brief  Sets a state as a root state
 *
 * This function sets the @p state in the @p ta as a root state. Note that
 * there might be multiple root states in a TA.
 *
 * @param[in,out]  ta     The TA to be altered
 * @param[in]      state  The state to be set as a root state in @p ta
 */
void vata_set_state_root(
	vata_ta_t*          ta,
	vata_state_t        state);


/**
 * @brief  Adds a transition into a TA
 *
 * This function adds a transition from the state @p parent to a tuple of
 * states passed in @p children (containing @p numChildren elements) over the
 * symbol @p symbol.(@p parent -> [@p symbol](@p children) ) into the TA @p ta.
 *
 * @param[in,out]  ta           The TA to be altered
 * @param[in]      parent       The parent state of the transition
 * @param[in]      symbol       The symbol of the transition
 * @param[in]      children     The children states of the transition
 * @param[in]      numChildren  The number of states in @p children
 */
void vata_add_transition(
	vata_ta_t*              ta,
	vata_state_t            parent,
	const vata_symbol_t*    symbol,
	const vata_state_t*     children,
	size_t                  numChildren);


/**
 * @brief  Prints the automaton
 *
 * @param[in]  ta  The automaton to be printed
 */
void vata_print_ta(
	const vata_ta_t*        ta);


#ifdef __cplusplus
	} // extern "C"
#endif

#endif /* LIBVATA_NOLL_IFACE_H_ */
