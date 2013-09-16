/**************************************************************************/
/*                                                                        */
/*  NOLL decision procedure                                               */
/*                                                                        */
/*  Copyright (C) 2013                                                    */
/*    LIAFA (University of Paris Diderot and CNRS)                        */
/*    TEAM (Brno University)                                              */
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
 * Defines translation between heap graph to time automata
 */
#ifndef NOLL_GRAPH2TA_H_
#define NOLL_GRAPH2TA_H_

//#include "ta.h" // Tree automata library
#include "noll_graph.h"

/* ====================================================================== */
/* Datatypes */
/* ====================================================================== */

/**
 * Type for tree automaton format used here.
 * TODO: define tree automaton type here or anywhere
 */
#define noll_ta_t  void

/* ====================================================================== */
/* Translators */
/* ====================================================================== */

noll_ta_t* noll_graph2ta(noll_graph_t* g);
/* Translates g into a tree automaton. */

#endif /* NOLL_GRAPH2TA_H_ */
