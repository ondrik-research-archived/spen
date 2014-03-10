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
/* Edge translators */
/* ====================================================================== */


/**
 * Get the TA for the edge built with predicate 'ls'
 * by instantiating the definition of the 
 * 'lso(in, out)' predicate (see ../samples/nll/ls-vc01.smt)
 *
 * lso(in, out) = (in = out) or
 *                (in != out and 
 *                 exists u . in -> {(f, u)} * lso(u, out))
 *
 * to the TA (q1 is a root state):
 *  q1 -> [f, in, m(f)](q2)
 *  q1 -> [lso, in, m(f)](q2)
 *  q2 -> [f, m(f)](q2)
 *  q2 -> [lso, m(f)](q2)
 *  q2 -> [out]
 * 
 * @param edge   An edge using the 'lso' predicate
 * @return       The TA recognizing unfolding of this edge
 */
noll_ta_t *
noll_edge2ta_ls (const noll_edge_t * edge)
{
  /* the checks on edge are done in the wrapper function */

  NOLL_DEBUG
    ("WARNING: Generating a fixed (and screwed-up) TA for the predicate lso\n");

  // get infos about the predicate 
  uint_t pid = edge->label;
  noll_pred_t *pred = noll_vector_at (preds_array, pid);
  assert (NULL != pred);

  /* find the unique field for the lso predicate */
  uid_t next_uid = UNDEFINED_ID;
  assert (NULL != pred->typ);
  assert (NULL != pred->typ->pfields);
  for (uint_t fid = 0; fid < noll_vector_size (fields_array); fid++)
    if (noll_vector_at (pred->typ->pfields, fid) == 1)
      {
	assert (next_uid == UNDEFINED_ID);
	next_uid = fid;
      }
  assert (UNDEFINED_ID != next_uid);

  vata_ta_t *ta = NULL;
  if ((ta = vata_create_ta ()) == NULL)
    {
      return NULL;
    }

  /* the set of selectors */
  noll_uid_array *selectors = noll_uid_array_new ();
  assert (NULL != selectors);
  noll_uid_array_push (selectors, next_uid);

  /* generic set of variables */
  noll_uid_array *vars1 = noll_uid_array_new ();

  /* identifiers for arguments */
  uid_t initial_node = noll_vector_at (edge->args, 0);
  uid_t end_node = noll_vector_at (edge->args, 1);

  /* fill the set of vars markings */
  assert (NULL != vars1);
  noll_uid_array_push (vars1, initial_node);

  /* marking1 = [eps] */
  noll_uid_array *marking1 = noll_uid_array_new ();
  assert (NULL != marking1);
  noll_uid_array_push (marking1, NOLL_MARKINGS_EPSILON);

  /* marking2 = [next, eps] */
  noll_uid_array *marking2 = noll_uid_array_new ();
  assert (NULL != marking2);
  noll_uid_array_copy (marking2, marking1);
  noll_uid_array_push (marking2, next_uid);

  /* vata_symbol_t* symbol_f_mf      = "<f> [m(f)]"; */
  const noll_ta_symbol_t *symbol_next1 =
    noll_ta_symbol_get_unique_allocated (selectors, vars1, marking1);
  assert (NULL != symbol_next1);

  /* vata_symbol_t* symbol_f_in_mf   = "<f> [in, m(f)]"; */
  const noll_ta_symbol_t *symbol_next2 =
    noll_ta_symbol_get_unique_allocated (selectors, NULL, marking2);
  assert (NULL != symbol_next2);

  /* vata_symbol_t* symbol_lso_mf    = "<lso> [m(f)]"; */
  const noll_ta_symbol_t *symbol_lso1 =
    noll_ta_symbol_get_unique_higher_pred (pred, vars1, marking1);
  assert (NULL != symbol_lso1);

  /* vata_symbol_t* symbol_lso_in_mf = "<lso> [in, m(f)]"; */
  const noll_ta_symbol_t *symbol_lso2 =
    noll_ta_symbol_get_unique_higher_pred (pred, NULL, marking2);
  assert (NULL != symbol_lso2);

  /* vata_symbol_t* symbol_out       = "<> [out]"; */
  const noll_ta_symbol_t *symbol_end =
    noll_ta_symbol_get_unique_aliased_var (end_node);
  assert (NULL != symbol_end);

  /* build the TA */
  vata_set_state_root (ta, 1);

  noll_uid_array *children = noll_uid_array_new ();
  noll_uid_array_push (children, 2);

  vata_add_transition (ta, 1, symbol_next1, children);
  vata_add_transition (ta, 1, symbol_lso1, children);
  vata_add_transition (ta, 2, symbol_next2, children);
  vata_add_transition (ta, 2, symbol_lso2, children);
  vata_add_transition (ta, 2, symbol_end, NULL);

  noll_uid_array_delete (marking1);
  noll_uid_array_delete (marking2);
  noll_uid_array_delete (vars1);
  noll_uid_array_delete (children);
  noll_uid_array_delete (selectors);

  return ta;
}

/**
 * Get the TA for the edge built with predicate 'ls'
 * by instantiating the definition of the
 * 'lsso(in, out)' predicate (see ../samples/nll/lss-vc01.smt)
 *
 * lsso(in, out) = (in = out) or
 *                 (in != out and 
 *                 exists u . in -> {(f1, u), (f2, u)} * lsso(u, out))
 *
 * to the TA (q1 is a root state):
 *  q1 -> [<f1,f2>, in, m(f)](q2,q3)
 *  q1 -> [lsso, in, m(f)](q2)
 *  q2 -> [<f1,f2>, m(f)](q2,q3)
 *  q2 -> [lsso, m(f)](q2)
 *  q2 -> [out]
 *  q3 -> [m(next2)]
 * 
 * @param edge   An edge using the 'lsso' predicate
 * @return       The TA recognizing unfolding of this edge
 */
noll_ta_t *
noll_edge2ta_lss (const noll_edge_t * edge)
{
  /* the checks on edge are done in the wrapper function */

  NOLL_DEBUG
    ("WARNING: Generating a fixed (and screwed-up) TA for the predicate lsso\n");

  // get infos about the predicate 
  uint_t pid = edge->label;
  noll_pred_t *pred = noll_vector_at (preds_array, pid);
  assert (NULL != pred);

  /* find the fields for the lsso predicate */
  uid_t next1_uid = UNDEFINED_ID;
  uid_t next2_uid = UNDEFINED_ID;
  assert (NULL != pred->typ);
  assert (NULL != pred->typ->pfields);
  for (uint_t fid = 0; fid < noll_vector_size (fields_array); fid++)
    if (noll_pred_is_field (pid, fid, NOLL_PFLD_BCKBONE))
      {
	if (next1_uid == UNDEFINED_ID)
	  next1_uid = fid;
	else if (next2_uid == UNDEFINED_ID)
	  next2_uid = fid;
	else
	  assert (false);
      }
  assert (UNDEFINED_ID != next1_uid);
  assert (UNDEFINED_ID != next2_uid);
  noll_field_t *next1_fld = noll_vector_at (fields_array, next1_uid);
  noll_field_t *next2_fld = noll_vector_at (fields_array, next2_uid);
  // this translation works only for the lsso predicate where 
  // next2 < next1 
  assert (noll_field_lt (next2_uid, next1_uid));

  vata_ta_t *ta = NULL;
  if ((ta = vata_create_ta ()) == NULL)
    {
      return NULL;
    }

  /* the set of selectors */
  noll_uid_array *selectors = noll_uid_array_new ();
  assert (NULL != selectors);
  noll_uid_array_push (selectors, next1_uid);
  noll_uid_array_push (selectors, next2_uid);

  /* generic set of variables */
  noll_uid_array *vars1 = noll_uid_array_new ();

  /* identifiers for arguments */
  uid_t initial_node = noll_vector_at (edge->args, 0);
  uid_t end_node = noll_vector_at (edge->args, 1);

  /* fill the set of vars markings */
  assert (NULL != vars1);
  noll_uid_array_push (vars1, initial_node);

  /* the marking [eps] */
  noll_uid_array *marking1 = noll_uid_array_new ();
  assert (NULL != marking1);
  noll_uid_array_push (marking1, NOLL_MARKINGS_EPSILON);

  /*  symbol [m(next2), eps]] */
  noll_uid_array *marking2 = noll_uid_array_new ();
  assert (NULL != marking2);
  noll_uid_array_copy (marking2, marking1);
  noll_uid_array_push (marking2, next2_uid);

  /* symbol <next1, next2> [in, eps] */
  const noll_ta_symbol_t *symbol_alloc1 =
    noll_ta_symbol_get_unique_allocated (selectors, vars1, marking1);
  assert (NULL != symbol_alloc1);

  /* symbol <lsso> [in, eps]  */
  const noll_ta_symbol_t *symbol_lsso1 =
    noll_ta_symbol_get_unique_higher_pred (pred, vars1, marking1);
  assert (NULL != symbol_lsso1);

  /* symbol <next1, next2> [m(next2), eps]  */
  const noll_ta_symbol_t *symbol_alloc2 =
    noll_ta_symbol_get_unique_allocated (selectors, NULL, marking2);
  assert (NULL != symbol_alloc2);

  /* symbol <lsso> [m(next2), eps]  */
  const noll_ta_symbol_t *symbol_lsso2 =
    noll_ta_symbol_get_unique_higher_pred (pred, NULL, marking2);
  assert (NULL != symbol_lsso2);

  /* symbol [out]  */
  const noll_ta_symbol_t *symbol_end =
    noll_ta_symbol_get_unique_aliased_var (end_node);
  assert (NULL != symbol_end);

  /* TODO: symbol [m(next2), eps]  */
  const noll_ta_symbol_t *symbol_ref =
    noll_ta_symbol_get_unique_aliased_marking (3, marking2);
  assert (NULL != symbol_ref);

  /* build the TA */
  vata_set_state_root (ta, 1);

  noll_uid_array *children1next = noll_uid_array_new ();
  noll_uid_array_push (children1next, 3);
  noll_uid_array_push (children1next, 2);

  noll_uid_array *children1lsso = noll_uid_array_new ();
  noll_uid_array_push (children1lsso, 2);

  noll_uid_array *children2next = noll_uid_array_new ();
  noll_uid_array_push (children2next, 3);
  noll_uid_array_push (children2next, 2);

  noll_uid_array *children2lsso = noll_uid_array_new ();
  noll_uid_array_push (children2lsso, 2);

  /* q1 -> <next1, next2> [in, eps] (q3,q2) */
  vata_add_transition (ta, 1, symbol_alloc1, children1next);
  /* q1 -> <lsso> [in, eps] (q2) */
  vata_add_transition (ta, 1, symbol_lsso1, children1lsso);
  /* q2 -> <next1, next2> [m(next2), eps] (q3,q2) */
  vata_add_transition (ta, 2, symbol_alloc2, children2next);
  /* q2 -> <lsso> [m(next2), eps] (q2) */
  vata_add_transition (ta, 2, symbol_lsso2, children2lsso);
  /* q2 -> [out] */
  vata_add_transition (ta, 2, symbol_end, NULL);
  /* q3 -> [m(next2)] */
  vata_add_transition (ta, 3, symbol_ref, NULL);

  noll_uid_array_delete (marking1);
  noll_uid_array_delete (marking2);
  noll_uid_array_delete (vars1);
  noll_uid_array_delete (children1next);
  noll_uid_array_delete (children1lsso);
  noll_uid_array_delete (children2next);
  noll_uid_array_delete (children2lsso);
  noll_uid_array_delete (selectors);

  return ta;
}

/**
 * Get the TA for the edge built with predicate 'dll'
 * by instantiating the definition of the
 * 'dll(in, out, prv, flw)' predicate (see ../samples/nll/dll-vc01.smt)
 *
 * dll(in,out,pv,fw) = ((in = fw) and (out=pv)) or
 *                 (in != fw and out != pv and
 *                 exists u. in -> {(next, u),(prev, pv)} * dll(u,out,in,fw))
 *
 * to the TA (q1 is a root state):
 * 
 *  -- only simple fields --
 *  q1 -> [<next,prev>, {in,out}, m(next)](q4,q5)
 *  q4 -> [,{fw},]()
 *  q5 -> [,{pv},]()
 *  q1 -> [<next,prev>, {in}, m(next)](q2,q5)
 *  q2 -> [<next,prev>, , m(next)](q2,q3)
 *  q3 -> [,s2(m(next)),]()
 *  q2 -> [<next,prev>, {out}, m(next)](q4,q3)
 *  
 *  -- only predicate segments --
 *  q1 -> [<dll>, {in}, m(next)](q6,q5)
 *  q6 -> [<next>, {out}, m(next)](q4)
 *  q1 -> [<dll>, {in}, m(next)](q7,q5)
 *  q7 -> [<next>, , m(next)](q8)
 *  q7 -> [<next>, {out}, m(next)](q4)
 *  q8 -> [<dll>, , m(next)](q7,q3)
 * 
 *  -- mixed fileds/dll --- 
 *  q7 -> [<next>, , m(next)](q2)
 *  q2 -> [<next>, , m(next)](q8)
 * 
 * @param edge   An edge using the 'lsso' predicate
 * @return       The TA recognizing unfolding of this edge
 */
noll_ta_t *
noll_edge2ta_dll (const noll_edge_t * edge)
{
  /* the checks on edge are done in the wrapper function */

  NOLL_DEBUG
    ("WARNING: Generating a fixed (and screwed-up) TA for the predicate dll\n");

  // get infos about the predicate 
  uint_t pid = edge->label;
  noll_pred_t *pred = noll_vector_at (preds_array, pid);
  assert (NULL != pred);

  /* find the fields for the dll predicate */
  uid_t next_uid = UNDEFINED_ID;
  uid_t prev_uid = UNDEFINED_ID;
  assert (NULL != pred->typ);
  assert (NULL != pred->typ->pfields);
  for (uint_t fid = 0; fid < noll_vector_size (fields_array); fid++)
    if (noll_pred_is_field (pid, fid, NOLL_PFLD_BCKBONE) &&
	(next_uid == UNDEFINED_ID))
      next_uid = fid;
    else if (noll_pred_is_field (pid, fid, NOLL_PFLD_BORDER) &&
	     (prev_uid == UNDEFINED_ID))
      prev_uid = fid;
    else
      assert (false);
  assert (UNDEFINED_ID != next_uid);
  assert (UNDEFINED_ID != prev_uid);
  assert (noll_field_lt (next_uid, prev_uid));

  /* identifiers for arguments */
  uid_t in_node = noll_vector_at (edge->args, 0);
  uid_t out_node = noll_vector_at (edge->args, 1);
  uid_t pv_node = noll_vector_at (edge->args, 2);
  uid_t fw_node = noll_vector_at (edge->args, 3);

  /* Start building the TA */
  vata_ta_t *ta = NULL;
  if ((ta = vata_create_ta ()) == NULL)
    {
      return NULL;
    }

  /*
   * Components of TA symbols
   */
  /* the list of fields */
  noll_uid_array *sel_next = noll_uid_array_new ();
  assert (NULL != sel_next);
  noll_uid_array_push (sel_next, next_uid);

  noll_uid_array *sel_prev = noll_uid_array_new ();
  assert (NULL != sel_prev);
  noll_uid_array_push (sel_prev, prev_uid);

  noll_uid_array *sel_next_prev = noll_uid_array_new ();
  assert (NULL != sel_next_prev);
  noll_uid_array_push (sel_next_prev, next_uid);
  noll_uid_array_push (sel_next_prev, prev_uid);

  /* sets of variables */
  noll_uid_array *vars_in = noll_uid_array_new ();
  assert (NULL != vars_in);
  noll_uid_array_push (vars_in, in_node);

  noll_uid_array *vars_out = noll_uid_array_new ();
  assert (NULL != vars_out);
  noll_uid_array_push (vars_out, out_node);

  noll_uid_array *vars_in_out = noll_uid_array_new ();
  assert (NULL != vars_in_out);
  noll_uid_array_push (vars_in_out, in_node);
  noll_uid_array_push (vars_in_out, out_node);

  noll_uid_array *vars_pv = noll_uid_array_new ();
  assert (NULL != vars_pv);
  noll_uid_array_push (vars_pv, pv_node);

  noll_uid_array *vars_fw = noll_uid_array_new ();
  assert (NULL != vars_fw);
  noll_uid_array_push (vars_fw, fw_node);

  /* the marking [eps] */
  noll_uid_array *mark_eps = noll_uid_array_new ();
  assert (NULL != mark_eps);
  noll_uid_array_push (mark_eps, NOLL_MARKINGS_EPSILON);

  /* the marking [m(next), eps]] */
  noll_uid_array *mark_next = noll_uid_array_new ();
  assert (NULL != mark_next);
  noll_uid_array_copy (mark_next, mark_eps);
  noll_uid_array_push (mark_next, next_uid);

  /* build the TA */
  vata_set_state_root (ta, 1);

  /* 
   * Transition: q1 -> [<next,prev>, {in,out}, m(next)](q4,q5)
   */
  const noll_ta_symbol_t *symbol_q1_1 =
    noll_ta_symbol_get_unique_allocated (sel_next_prev, vars_in_out,
					 mark_eps);
  assert (NULL != symbol_q1_1);
  noll_uid_array *succ_q1 = noll_uid_array_new ();
  noll_uid_array_push (succ_q1, 4);
  noll_uid_array_push (succ_q1, 5);
  vata_add_transition (ta, 1, symbol_q1_1, succ_q1);
  noll_uid_array_delete (succ_q1);

  /*
   * Transition: q1 -> [<next,prev>, {in}, m(next)](q2,q5)
   */
  const noll_ta_symbol_t *symbol_q1_2 =
    noll_ta_symbol_get_unique_allocated (sel_next_prev, vars_in, mark_eps);
  assert (NULL != symbol_q1_2);
  succ_q1 = noll_uid_array_new ();
  noll_uid_array_push (succ_q1, 2);
  noll_uid_array_push (succ_q1, 5);
  vata_add_transition (ta, 1, symbol_q1_2, succ_q1);
  noll_uid_array_delete (succ_q1);

  /*
   * Transition: q1 -> [<dll>, {in}, m(next)](q6,q5)
   */
  const noll_ta_symbol_t *symbol_q1_3 =
    noll_ta_symbol_get_unique_higher_pred (pred, vars_in, mark_eps);
  assert (NULL != symbol_q1_3);
  succ_q1 = noll_uid_array_new ();
  noll_uid_array_push (succ_q1, 6);
  noll_uid_array_push (succ_q1, 5);
  vata_add_transition (ta, 1, symbol_q1_3, succ_q1);
  noll_uid_array_delete (succ_q1);

  /*
   * Transition: q1 -> [<dll>, {in}, m(next)](q7,q5)
   */
  const noll_ta_symbol_t *symbol_q1_4 =
    noll_ta_symbol_get_unique_higher_pred (pred, vars_in, mark_eps);
  assert (NULL != symbol_q1_4);
  succ_q1 = noll_uid_array_new ();
  noll_uid_array_push (succ_q1, 7);
  noll_uid_array_push (succ_q1, 5);
  vata_add_transition (ta, 1, symbol_q1_4, succ_q1);
  noll_uid_array_delete (succ_q1);

  /*
   * Transition: q2 -> [<next,prev>, , m(next)](q2,q3)
   */
  const noll_ta_symbol_t *symbol_q2_1 =
    noll_ta_symbol_get_unique_allocated (sel_next_prev, NULL, mark_next);
  assert (NULL != symbol_q2_1);
  noll_uid_array *succ_q2 = noll_uid_array_new ();
  noll_uid_array_push (succ_q2, 2);
  noll_uid_array_push (succ_q2, 3);
  vata_add_transition (ta, 2, symbol_q2_1, succ_q2);
  noll_uid_array_delete (succ_q2);

  /*
   * Transition: q2 -> [<next,prev>, {out}, m(next)](q4,q3)
   */
  const noll_ta_symbol_t *symbol_q2_2 =
    noll_ta_symbol_get_unique_allocated (sel_next_prev, vars_out, mark_eps);
  assert (NULL != symbol_q2_2);
  succ_q2 = noll_uid_array_new ();
  noll_uid_array_push (succ_q2, 4);
  noll_uid_array_push (succ_q2, 3);
  vata_add_transition (ta, 2, symbol_q2_2, succ_q2);
  noll_uid_array_delete (succ_q2);

  /* 
   * Transition:  q2 -> [<next>, , m(next)](q8)
   */
  const noll_ta_symbol_t *symbol_q2_3 =
    noll_ta_symbol_get_unique_allocated (sel_next, NULL, mark_next);
  assert (NULL != symbol_q2_3);
  succ_q2 = noll_uid_array_new ();
  noll_uid_array_push (succ_q2, 8);
  vata_add_transition (ta, 2, symbol_q2_3, succ_q2);
  noll_uid_array_delete (succ_q2);

  /*
   * Transition: q3 -> [,s2(m(next)),]()
   */
  const noll_ta_symbol_t *symbol_q3 =
    noll_ta_symbol_get_unique_aliased_marking (2, mark_next);
  assert (NULL != symbol_q3);
  noll_uid_array *succ_empty = noll_uid_array_new ();
  vata_add_transition (ta, 3, symbol_q3, succ_empty);

  /*
   * Transition: q4 -> [,{fw},]()
   */
  const noll_ta_symbol_t *symbol_q4 =
    noll_ta_symbol_get_unique_allocated (NULL, vars_fw, mark_eps);
  assert (NULL != symbol_q4);
  vata_add_transition (ta, 4, symbol_q4, succ_empty);

  /*
   * Transition: q5 -> [,{pv},]()
   */
  const noll_ta_symbol_t *symbol_q5 =
    noll_ta_symbol_get_unique_allocated (NULL, vars_pv, mark_eps);
  assert (NULL != symbol_q5);
  vata_add_transition (ta, 5, symbol_q5, succ_empty);
  noll_uid_array_delete (succ_empty);

  /*
   * Transition: q6 -> [<next>, {out}, m(next)](q4)
   */
  const noll_ta_symbol_t *symbol_q6 =
    noll_ta_symbol_get_unique_allocated (sel_next, vars_out, mark_eps);
  assert (NULL != symbol_q6);
  noll_uid_array *succ_q6 = noll_uid_array_new ();
  noll_uid_array_push (succ_q6, 4);
  vata_add_transition (ta, 6, symbol_q6, succ_q6);
  noll_uid_array_delete (succ_q6);

  /*
   * Transition: q7 -> [<next>, , m(next)](q8)
   */
  const noll_ta_symbol_t *symbol_q7_1 =
    noll_ta_symbol_get_unique_allocated (sel_next, NULL, mark_next);
  assert (NULL != symbol_q7_1);
  noll_uid_array *succ_q7 = noll_uid_array_new ();
  noll_uid_array_push (succ_q7, 8);
  vata_add_transition (ta, 7, symbol_q7_1, succ_q7);
  noll_uid_array_delete (succ_q7);

  /*
   * Transition: q7 -> [<next>, {out}, m(next)](q4)
   */
  const noll_ta_symbol_t *symbol_q7_2 =
    noll_ta_symbol_get_unique_allocated (sel_next, vars_out, mark_eps);
  assert (NULL != symbol_q7_2);
  succ_q7 = noll_uid_array_new ();
  noll_uid_array_push (succ_q7, 4);
  vata_add_transition (ta, 7, symbol_q7_2, succ_q7);
  noll_uid_array_delete (succ_q7);

  /*
   * Transition: q7 -> [<next>, , m(next)](q2)
   */
  const noll_ta_symbol_t *symbol_q7_3 =
    noll_ta_symbol_get_unique_allocated (sel_next, NULL, mark_next);
  assert (NULL != symbol_q7_3);
  succ_q7 = noll_uid_array_new ();
  noll_uid_array_push (succ_q7, 2);
  vata_add_transition (ta, 7, symbol_q7_3, succ_q7);
  noll_uid_array_delete (succ_q7);

  /*
   * Transition: q8 -> [<dll>, , m(next)](q7,q3)
   */
  const noll_ta_symbol_t *symbol_q8 =
    noll_ta_symbol_get_unique_higher_pred (pred, NULL, mark_next);
  assert (NULL != symbol_q8);
  noll_uid_array *succ_q8 = noll_uid_array_new ();
  noll_uid_array_push (succ_q1, 7);
  noll_uid_array_push (succ_q1, 3);
  vata_add_transition (ta, 8, symbol_q8, succ_q8);
  noll_uid_array_delete (succ_q8);


  noll_uid_array_delete (mark_eps);
  noll_uid_array_delete (mark_next);
  noll_uid_array_delete (vars_in);
  noll_uid_array_delete (vars_out);
  noll_uid_array_delete (vars_in_out);
  noll_uid_array_delete (vars_fw);
  noll_uid_array_delete (vars_pv);
  noll_uid_array_delete (sel_next);
  noll_uid_array_delete (sel_next_prev);
  noll_uid_array_delete (sel_prev);

  return ta;
}

noll_ta_t *
noll_edge2ta_nll (const noll_edge_t * edge)
{
  assert (NULL != edge);
  NOLL_DEBUG ("ERROR: translation for predicate nll not implemented!\n");
  return NULL;			// TODO
}

noll_ta_t *
noll_edge2ta_skl (const noll_edge_t * edge)
{
  assert (NULL != edge);
  NOLL_DEBUG ("ERROR: translation for predicate skl not implemented!\n");
  return NULL;			// TODO
}



/**
 * Get the TA for the @p edge.  
 * 
 * @param edge    A predicate edge
 * @return        A TA recorgnizing the tree encodings for this edge
 */
noll_ta_t *
noll_edge2ta (const noll_edge_t * edge)
{
  assert (NULL != edge);
  assert (NOLL_EDGE_PRED == edge->kind);
  assert (2 <= noll_vector_size (edge->args));

  const uid_t pid = edge->label;
  const noll_pred_t *pred = noll_pred_getpred (edge->label);
  assert (NULL != pred);
  assert (NULL != pred->pname);
  assert (NULL != pred->def);
  assert (noll_vector_size (edge->args) == pred->def->fargs);

  NOLL_DEBUG
    ("********************************************************************************\n");
  NOLL_DEBUG
    ("*                                 EDGE -> TA                                   *\n");
  NOLL_DEBUG
    ("********************************************************************************\n");

  vata_ta_t *ta = NULL;
  if ((ta = vata_create_ta ()) == NULL)
    {
      return NULL;
    }

  NOLL_DEBUG ("Edge: args = %u\n", noll_vector_size (edge->args));
  NOLL_DEBUG ("  args[0] = %u\n", noll_vector_at (edge->args, 0));
  NOLL_DEBUG ("  args[1] = %u\n", noll_vector_at (edge->args, 1));

  NOLL_DEBUG ("Exposing the predicate structure\n");
  NOLL_DEBUG ("Name: %s\n", pred->pname);
  const noll_pred_binding_t *def = pred->def;
  assert (NULL != def);
  NOLL_DEBUG ("definition:\n");
  NOLL_DEBUG ("  arguments: %lu\n", def->pargs);
  NOLL_DEBUG ("  formal arguments: %u\n", def->fargs);

  assert (NULL != def->sigma_0);
  NOLL_DEBUG ("Sigma_0 kind: %u\n", def->sigma_0->kind);
  NOLL_DEBUG ("Sigma_0 is precise: %s\n",
	      def->sigma_0->is_precise ? "true" : "false");

  //MS: changed to support nll!
  if (NULL == def->sigma_1)
    NOLL_DEBUG ("Sigma_1: empty\n");
  else
    {
      NOLL_DEBUG ("Sigma_1: predicate with nesting\n");
      NOLL_DEBUG ("Sigma_1 kind: %u\n", def->sigma_1->kind);
      NOLL_DEBUG ("Sigma_1 is precise: %s\n",
		  def->sigma_1->is_precise ? "true" : "false");
    }

  if (0 == strcmp (pred->pname, "lso"))
    {				// this is the "ls" predicate

      ta = noll_edge2ta_ls (edge);
    }
  else if (0 == strcmp (pred->pname, "lsso"))
    {
      ta = noll_edge2ta_lss (edge);
    }
  else if (0 == strcmp (pred->pname, "dll"))
    {
      ta = noll_edge2ta_dll (edge);
    }
  else if (0 == strcmp (pred->pname, "nll"))
    {
      ta = noll_edge2ta_nll (edge);
    }
  else if (0 == strncmp (pred->pname, "skl", 3))
    {
      ta = noll_edge2ta_skl (edge);
    }
  else
    {
      NOLL_DEBUG ("ERROR: translation for predicate %s not implemented!\n",
		  pred->pname);
      assert (false);
    }

  NOLL_DEBUG ("Generated TA for edge:\n");
#ifndef NDEBUG
  vata_print_ta (ta);
#endif
  NOLL_DEBUG ("*** END EDGE -> TA\n");


  return ta;
}
