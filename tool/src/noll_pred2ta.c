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

#include "noll.h"
#include "libvata_noll_iface.h"
#include "noll_pred2ta.h"

/* ====================================================================== */
/* Translators */
/* ====================================================================== */

/**
 *  Translates a predicate into a tree automaton.
 *  @return TA built or NULL
 */
vata_ta_t* noll_pred2ta(const noll_pred_t* p) {
  assert(NULL != p);

  vata_ta_t* ta = NULL;
  if ((ta = vata_create_ta()) == NULL)
  {
    return NULL;
  }

  // now, we translate the 'lso(in, out)' predicate (see
  // ../samples/nll/ls-vc01.smt)
  //
  //   lso(in, out) = \exists u . in -> {(f, u)} * ((u = out) \/ lso(u, out))
  //
  // to a TA (q1 is a root state):
  //
  //   q1 -> [f, in, m(f)](q2)
  //   q1 -> [lso, in, m(f)](q2)
  //   q2 -> [f, m(f)](q2)
  //   q2 -> [lso, m(f)](q2)
  //   q2 -> [out]
  //

	NOLL_DEBUG("WARNING: Generating fixed TA for the predicate lso\n");
  vata_set_state_root(ta, 1);

  vata_state_t children[] = {2};

  // here, we should add the symbols into a list (tree? some other set?)

  vata_symbol_t* symbol_f_in_mf   = "<f> [in, m(f)]";
  vata_symbol_t* symbol_lso_in_mf = "<lso> [in, m(f)]";
  vata_symbol_t* symbol_f_mf      = "<f> [m(f)]";
  vata_symbol_t* symbol_lso_mf    = "<lso> [m(f)]";
  vata_symbol_t* symbol_out       = "<> [out]";

  vata_add_transition(ta, 1, symbol_f_in_mf  , children, 1);
  vata_add_transition(ta, 1, symbol_lso_in_mf, children, 1);
  vata_add_transition(ta, 2, symbol_f_mf     , children, 1);
  vata_add_transition(ta, 2, symbol_lso_mf   , children, 1);
  vata_add_transition(ta, 2, symbol_out      , NULL    , 0);

	return ta;
}
