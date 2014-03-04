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

/**
 * Defines translation between heap graph to tree automata
 */
#ifndef NOLL_PRED2TA_H_
#define NOLL_PRED2TA_H_

//#include "ta.h" // Tree automata library
#include "noll_preds.h"
#include "noll_graph2ta.h"

/* ====================================================================== */
/* Datatypes */
/* ====================================================================== */

/**
 * Type for tree automaton format used here.
 * TODO: define tree automaton type here or anywhere
 */

/* ====================================================================== */
/* Translators */
/* ====================================================================== */

noll_ta_t* noll_pred2ta(const noll_pred_t* p);
/* Translates predicate p to a ta with formal parameters */

/**
 * @brief  Translates a higher-order predicate dedge into a TA
 *
 * @param[in]  edge  The edge to be translated
 *
 * @returns  A TA representing all models that the edge denotes
 */
noll_ta_t* noll_edge2ta(
	const noll_edge_t*               edge);

#endif /* NOLL_PRED2TA_H_ */
