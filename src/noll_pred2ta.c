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

noll_ta_t* noll_edge2ta(
	const noll_edge_t*               edge)
{
	assert(NULL != edge);
	assert(NOLL_EDGE_PRED == edge->kind);

	const noll_pred_t* pred = noll_pred_getpred(edge->label);
	assert(NULL != pred);
	assert(NULL != pred->pname);

	NOLL_DEBUG("********************************************************************************\n");
	NOLL_DEBUG("*                                 EDGE -> TA                                   *\n");
	NOLL_DEBUG("********************************************************************************\n");

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

	NOLL_DEBUG("Exposing the predicate structure\n");
	NOLL_DEBUG("Name: %s\n", pred->pname);
	const noll_pred_binding_t* def = pred->def;
	assert(NULL != def);
	NOLL_DEBUG("definition:\n");
	NOLL_DEBUG("  arguments: %lu\n", def->pargs);
	NOLL_DEBUG("  formal arguments: %u\n", def->fargs);
	assert(NULL != def->sigma_0);

	// just one points-to!
	assert(NULL == def->sigma_1);

	NOLL_DEBUG("Sigma_0 kind: %u\n", def->sigma_0->kind);
	NOLL_DEBUG("Sigma_0 is precise: %s\n", def->sigma_0->is_precise? "true":"false");

	if (0 == strcmp(pred->pname, "lso"))
	{	// this is the "ls" predicate
		NOLL_DEBUG("WARNING: Generating a fixed (and screwed-up) TA for the predicate lso\n");
		vata_set_state_root(ta, 1);

		noll_uid_array* children = noll_uid_array_new();
		noll_uid_array_push(children, 2);

		// here, we should add the symbols into a list (tree? some other set?)

		/* vata_symbol_t* symbol_f_in_mf   = "<f> [in, m(f)]"; */
		/* vata_symbol_t* symbol_lso_in_mf = "<lso> [in, m(f)]"; */
		/* vata_symbol_t* symbol_f_mf      = "<f> [m(f)]"; */
		/* vata_symbol_t* symbol_lso_mf    = "<lso> [m(f)]"; */
		/* vata_symbol_t* symbol_out       = "<> [out]"; */

		// this works only for the lso predicate
		uid_t f_uid = noll_field_array_find("next");
		assert(UNDEFINED_ID != f_uid);

		noll_uid_array* selectors = noll_uid_array_new();
		assert(NULL != selectors);
		noll_uid_array_push(selectors, f_uid);

		noll_uid_array* vars = noll_uid_array_new();
		assert(NULL != vars);

		noll_uid_array* marking = noll_uid_array_new();
		assert(NULL != marking);

		const noll_ta_symbol_t* symbol_f = noll_ta_symbol_get_unique_allocated(
			selectors, vars, marking);

		const noll_ta_symbol_t* symbol_lso = noll_ta_symbol_get_unique_higher_pred(
			pred, vars, marking);

		vata_add_transition(ta, 1, symbol_f    , children);
		vata_add_transition(ta, 1, symbol_lso  , children);
		/* vata_add_transition(ta, 1, symbol_lso_in_mf, children, 1); */
		vata_add_transition(ta, 2, symbol_f    , children);
		vata_add_transition(ta, 2, symbol_lso  , children);
		/* vata_add_transition(ta, 2, symbol_lso_mf   , children, 1); */

		noll_uid_array_delete(marking);
		noll_uid_array_delete(vars);
		noll_uid_array_delete(children);
		noll_uid_array_delete(selectors);
	}
	else if (0 == strcmp(pred->pname, "lsso"))
	{
		NOLL_DEBUG("WARNING: Generating a fixed (and screwed-up) TA for the predicate lso\n");
		vata_set_state_root(ta, 1);

		noll_uid_array* children = noll_uid_array_new();
		noll_uid_array_push(children, 2);
		noll_uid_array_push(children, 3);

		// here, we should add the symbols into a list (tree? some other set?)

		/* vata_symbol_t* symbol_f_in_mf   = "<f> [in, m(f)]"; */
		/* vata_symbol_t* symbol_lso_in_mf = "<lso> [in, m(f)]"; */
		/* vata_symbol_t* symbol_f_mf      = "<f> [m(f)]"; */
		/* vata_symbol_t* symbol_lso_mf    = "<lso> [m(f)]"; */
		/* vata_symbol_t* symbol_out       = "<> [out]"; */

		// this works only for the lso predicate
		uid_t next1_uid = noll_field_array_find("next1");
		assert(UNDEFINED_ID != next1_uid);
		uid_t next2_uid = noll_field_array_find("next2");
		assert(UNDEFINED_ID != next2_uid);

		noll_uid_array* selectors = noll_uid_array_new();
		assert(NULL != selectors);
		noll_uid_array_push(selectors, next1_uid);
		noll_uid_array_push(selectors, next2_uid);

		noll_uid_array* vars = noll_uid_array_new();
		assert(NULL != vars);

		noll_uid_array* marking = noll_uid_array_new();
		assert(NULL != marking);

		const noll_ta_symbol_t* symbol_alloc = noll_ta_symbol_get_unique_allocated(
			selectors, vars, marking);

		const noll_ta_symbol_t* symbol_lsso = noll_ta_symbol_get_unique_higher_pred(
			pred, vars, marking);

		vata_add_transition(ta, 1, symbol_alloc    , children);
		vata_add_transition(ta, 1, symbol_lsso  , children);
		/* vata_add_transition(ta, 1, symbol_lso_in_mf, children, 1); */
		vata_add_transition(ta, 2, symbol_alloc    , children);
		vata_add_transition(ta, 2, symbol_lsso  , children);
		/* vata_add_transition(ta, 2, symbol_lso_mf   , children, 1); */

		noll_uid_array_delete(marking);
		noll_uid_array_delete(vars);
		noll_uid_array_delete(children);
		noll_uid_array_delete(selectors);
	}
	else
	{
		NOLL_DEBUG("ERROR: translation for predicate %s not implemented!\n", pred->pname);
		assert(false);
	}

	return ta;
}
