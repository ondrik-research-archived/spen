/**************************************************************************/
/*                                                                        */
/*  NOLL decision procedure                                               */
/*                                                                        */
/*  Copyright (C) 2012-2013                                               */
/*    LIAFA (University of Paris Diderot and CNRS)                        */
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
 * Homomorphism definition and computation.
 */


#ifndef NOLL_HOM_H_
#define NOLL_HOM_H_

#include <stdio.h>
#include "noll_graph.h"
#include "noll_graph2ta.h"


/* ====================================================================== */
/* Datatypes */
/* ====================================================================== */

// TODO: extract homomorphism type
#define noll_hom_t  void

/* ====================================================================== */
/* Constructors/destructors */
/* ====================================================================== */


/* ====================================================================== */
/* Getters/Setters */
/* ====================================================================== */


/* ====================================================================== */
/* Printers */
/* ====================================================================== */

void noll_hom_fprint(FILE* f, noll_hom_t* h);

/* ====================================================================== */
/* Solver */
/* ====================================================================== */

int noll_graph_homomorphism(noll_graph_t* g1, noll_graph_t* g2);
/* Search an homomorphism from g1 (neg) to g2 (pos) to prove g2 |= g1. */
/*TODO
 * Returns 0 if there is no homomorphism from g1 to g2,
 * otherwise (a homomorphism exists) it updates
 * sharing constraints in g2 with the substitution given by the
 * edge mapping in the homomorphism.
 */


#endif /* NOLL_HOM_H_ */
