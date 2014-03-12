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

uint_t noll_pred2ta_ls(noll_ta_t* ta, noll_pred_t* pred, uid_t fid,
           uint_t qinit, 
           noll_uid_array* vars_in, noll_uid_array* mark_in,
           noll_uid_array* vars_out, unsigned char alias_out);
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

  /* build the TA */
  vata_ta_t *ta = NULL;
  if ((ta = vata_create_ta ()) == NULL)
    {
      return NULL;
    }
  vata_set_state_root (ta, 1);

  /* identifiers for arguments */
  uid_t initial_node = noll_vector_at (edge->args, 0);
  uid_t end_node = noll_vector_at (edge->args, 1);

  /* label of in variables */
  noll_uid_array *vars_in = noll_uid_array_new ();
  assert (NULL != vars_in);
  noll_uid_array_push (vars_in, initial_node);

  /* label of out variables */
  noll_uid_array *vars_out = noll_uid_array_new ();
  assert (NULL != vars_out);
  noll_uid_array_push (vars_out, end_node);

  /* empty marking for first state, mark_eps = [eps] */
  noll_uid_array *mark_eps = noll_uid_array_new ();
  assert (NULL != mark_eps);
  noll_uid_array_push (mark_eps, NOLL_MARKINGS_EPSILON);

  uint_t qend = noll_pred2ta_ls(ta, pred, next_uid, 1, vars_in, mark_eps, vars_out, 0); 
  
  ///* the set of selectors */
  //noll_uid_array *selectors = noll_uid_array_new ();
  //assert (NULL != selectors);
  //noll_uid_array_push (selectors, next_uid);

  ///* marking2 = [next, eps] */
  //noll_uid_array *marking2 = noll_uid_array_new ();
  //assert (NULL != marking2);
  //noll_uid_array_copy (marking2, marking1);
  //noll_uid_array_push (marking2, next_uid);

  ///* vata_symbol_t* symbol_f_mf      = "<f> [m(f)]"; */
  //const noll_ta_symbol_t *symbol_next1 =
    //noll_ta_symbol_get_unique_allocated (selectors, vars1, marking1);
  //assert (NULL != symbol_next1);

  ///* vata_symbol_t* symbol_f_in_mf   = "<f> [in, m(f)]"; */
  //const noll_ta_symbol_t *symbol_next2 =
    //noll_ta_symbol_get_unique_allocated (selectors, NULL, marking2);
  //assert (NULL != symbol_next2);

  ///* vata_symbol_t* symbol_lso_mf    = "<lso> [m(f)]"; */
  //const noll_ta_symbol_t *symbol_lso1 =
    //noll_ta_symbol_get_unique_higher_pred (pred, vars1, marking1);
  //assert (NULL != symbol_lso1);

  ///* vata_symbol_t* symbol_lso_in_mf = "<lso> [in, m(f)]"; */
  //const noll_ta_symbol_t *symbol_lso2 =
    //noll_ta_symbol_get_unique_higher_pred (pred, NULL, marking2);
  //assert (NULL != symbol_lso2);

  ///* vata_symbol_t* symbol_out       = "<> [out]"; */
  //const noll_ta_symbol_t *symbol_end =
    //noll_ta_symbol_get_unique_aliased_var (end_node);
  //assert (NULL != symbol_end);

  ///* build the TA */
  //vata_set_state_root (ta, 1);

  //noll_uid_array *children = noll_uid_array_new ();
  //noll_uid_array_push (children, 2);

  //vata_add_transition (ta, 1, symbol_next1, children);
  //vata_add_transition (ta, 1, symbol_lso1, children);
  //vata_add_transition (ta, 2, symbol_next2, children);
  //vata_add_transition (ta, 2, symbol_lso2, children);
  //vata_add_transition (ta, 2, symbol_end, NULL);

  //noll_uid_array_delete (marking1);
  //noll_uid_array_delete (marking2);
  //noll_uid_array_delete (vars1);
  //noll_uid_array_delete (children);
  //noll_uid_array_delete (selectors);

  noll_uid_array_delete (mark_eps);
  noll_uid_array_delete (vars_in);
  noll_uid_array_delete (vars_out);
  
  return ta;
}


/**
 * Add to the @p ta the transitions encoding the ls predicate,
 * starting from state @p qinit, labeling the first state by @p vars_in,
 * ending in @p vars_out, and marking the first state by @p mark_in.
 * 
 * @param ta       the TA to which transitions are added
 * @param pred     the predicate generated
 * @param fid      the field to be used as selector
 * @param qinit    the initial state to which transitions are added
 * @param vars_in  labeling of initial state
 * @param mark_in  marking of the initial state
 * @param mark_out marking of output state
 * @param alias_out aliasing of the output state
 * @return         the number of the last state generated for @p ta
 */
uint_t 
noll_pred2ta_ls(noll_ta_t* ta, noll_pred_t* pred, uid_t fid,
                uint_t qinit, 
                noll_uid_array* vars_in, noll_uid_array* mark_in,
                noll_uid_array* mark_out, unsigned char alias_out)
{
    
  NOLL_DEBUG
    ("WARNING: Generating a nested TA for the predicate ls\n");

  assert (NULL != ta);
  assert (NULL != mark_in); // at least eps
  assert (NULL != mark_out); // at least one marking
  assert (noll_vector_size(mark_out) >= 1);
  
  uint_t q = qinit;
  
  /* the selectors */
  noll_uid_array *selectors = noll_uid_array_new ();
  assert (NULL != selectors);
  noll_uid_array_push (selectors, fid);

  /* the marking used mark_in_fld = mark_in . fld */
  noll_uid_array *mark_in_fld = noll_uid_array_new ();
  assert (NULL != mark_in_fld);
  noll_uid_array_copy (mark_in_fld, mark_in);
  noll_uid_array_push (mark_in_fld, fid);

  q = q+1; /* next state is qinit + 1 */
  noll_uid_array *children = noll_uid_array_new ();
  noll_uid_array_push (children, q);

  /* 
   * Transition: q1 -> [<fid>, {in}, mark_in](q2) 
   *       -- one cell
   */
  const noll_ta_symbol_t *symbol_next1 =
    noll_ta_symbol_get_unique_allocated (selectors, vars_in, mark_in);
  assert (NULL != symbol_next1);
  vata_add_transition (ta, qinit, symbol_next1, children);

  /* 
   * Transition: q1 -> [<ls>, {in}, mark_in](q2) 
   *       -- one list segment
   */
  const noll_ta_symbol_t *symbol_lso1 =
    noll_ta_symbol_get_unique_higher_pred (pred, vars_in, mark_in);
  assert (NULL != symbol_lso1);
  vata_add_transition (ta, qinit, symbol_lso1, children);

  /* 
   * Transition: q2 -> [<fid>, {}, mark_in_fld](q2) 
   *       -- one list segment
   */  
  const noll_ta_symbol_t *symbol_next2 =
    noll_ta_symbol_get_unique_allocated (selectors, NULL, mark_in_fld);
  assert (NULL != symbol_next2);
  vata_add_transition (ta, q, symbol_next2, children);

  /* 
   * Transition: q2 -> [<ls>, {}, mark_in_fld](q2) 
   *       -- one list segment
   */  
  const noll_ta_symbol_t *symbol_lso2 =
    noll_ta_symbol_get_unique_higher_pred (pred, NULL, mark_in_fld);
  assert (NULL != symbol_lso2);
  vata_add_transition (ta, q, symbol_lso2, children);

  /* 
   * Transition: q2 -> [, {out}, ]() 
   *       -- one list segment
   */  
  const noll_ta_symbol_t *symbol_end = NULL;
  if (alias_out == 0)
    symbol_end = 
      noll_ta_symbol_get_unique_aliased_var (noll_vector_at(mark_out,0));
  else
    symbol_end =
      noll_ta_symbol_get_unique_aliased_marking (alias_out, mark_out);
  assert (NULL != symbol_end);
  vata_add_transition (ta, q, symbol_end, NULL);

  noll_uid_array_delete (mark_in_fld);
  noll_uid_array_delete (children);
  noll_uid_array_delete (selectors);

  return q;
}
    
/**
 * Get the TA for the edge built with predicate 'lss'
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
 * (Notice: both int and out are 'allocated' on the list segment!)
 * 
 * to the TA (q1 is a root state):
 * 
 *  -- only simple fields --
 *  q1 -> [<next,prev>, {in,out}, eps](q4,q5)
 *        -- one cell list 
 *  q1 -> [<next,prev>, {in}, eps](q2,q5)
 *        -- at least two cell list 
 *  q2 -> [<next,prev>, {out}, m(next)](q4,q6)
 *        -- exactly two cells
 *  q2 -> [<next,prev>, , m(next)](q3,q6)
 *        -- more than two cells
 *  q3 -> [<next,prev>, , m(next)](q3,q7)
 *        -- inner cells after two
 *  q3 -> [<next,prev>, {out}, m(next)](q4,q7)
 *        -- end cell after two
 *  q4 -> [,{fw},]()
 *        -- ref to foward var
 *  q5 -> [,{pv},]()
 *        -- ref to prev var
 *  q6 -> [,s2(eps),]()
 *        -- ref to the input of the list
 *  q7 -> [,s2(m(next)),]()
 *        -- ref to the previous inside the list
 *  
 *  -- only predicate segments --
 *  q1 -> [<dll>, {in}, eps](q8,q5)
 *        -- one list segment from in location
 *  q8 -> [<next>, {out}, m(next)](q4)
 *        -- end of list segment dll
 *  q8 -> [<next>, , m(next)](q9)
 *        -- link by next to another dll cell
 *  q9 -> [<dll>, , m(next)](q8,q7)
 * 
 *  -- mixed fileds/dll --- 
 *  q9 -> [<next>, , m(next)](q3)
 *  q3 -> [<next>, , m(next)](q9)
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
   * Transition: q1 -> [<next,prev>, {in,out}, eps](q4,q5)
   *        -- one cell list 
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
   * Transition: q1 -> [<next,prev>, {in}, eps](q2,q5)
   *        -- at least two cell list 
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
   * Transition: q1 -> [<dll>, {in}, eps](q8,q5)
   *        -- one list segment from in location
   */
  const noll_ta_symbol_t *symbol_q1_3 =
    noll_ta_symbol_get_unique_higher_pred (pred, vars_in, mark_eps);
  assert (NULL != symbol_q1_3);
  succ_q1 = noll_uid_array_new ();
  noll_uid_array_push (succ_q1, 8);
  noll_uid_array_push (succ_q1, 5);
  vata_add_transition (ta, 1, symbol_q1_3, succ_q1);
  noll_uid_array_delete (succ_q1);

  /*
   * Transition: q2 -> [<next,prev>, {out}, m(next)](q4,q6)
   *        -- exactly two cells
   */
  const noll_ta_symbol_t *symbol_q2_1 =
    noll_ta_symbol_get_unique_allocated (sel_next_prev, vars_out, mark_next);
  assert (NULL != symbol_q2_1);
  noll_uid_array *succ_q2 = noll_uid_array_new ();
  noll_uid_array_push (succ_q2, 4);
  noll_uid_array_push (succ_q2, 6);
  vata_add_transition (ta, 2, symbol_q2_1, succ_q2);
  noll_uid_array_delete (succ_q2);

  /*
   * Transition: q2 -> [<next,prev>, , m(next)](q3,q6)
   *         -- more than two cells
   */
  const noll_ta_symbol_t *symbol_q2_2 =
    noll_ta_symbol_get_unique_allocated (sel_next_prev, NULL, mark_next);
  assert (NULL != symbol_q2_2);
  succ_q2 = noll_uid_array_new ();
  noll_uid_array_push (succ_q2, 3);
  noll_uid_array_push (succ_q2, 6);
  vata_add_transition (ta, 2, symbol_q2_2, succ_q2);
  noll_uid_array_delete (succ_q2);

  /* 
   * Transition: q3 -> [<next,prev>, , m(next)](q3,q7)
   *        -- inner cells after two
   */
  const noll_ta_symbol_t *symbol_q3_1 =
    noll_ta_symbol_get_unique_allocated (sel_next_prev, NULL, mark_next);
  assert (NULL != symbol_q3_1);
  noll_uid_array* succ_q3 = noll_uid_array_new ();
  noll_uid_array_push (succ_q3, 3);
  noll_uid_array_push (succ_q3, 7);
  vata_add_transition (ta, 3, symbol_q3_1, succ_q3);
  noll_uid_array_delete (succ_q3);

  /*
   * Transition: q3 -> [<next,prev>, {out}, m(next)](q4,q7)
   *        -- end cell after two
   */
  const noll_ta_symbol_t *symbol_q3_2 =
    noll_ta_symbol_get_unique_allocated (sel_next_prev, vars_out, mark_next);
  assert (NULL != symbol_q3_2);
  succ_q3 = noll_uid_array_new ();
  noll_uid_array_push (succ_q3, 4);
  noll_uid_array_push (succ_q3, 7);
  vata_add_transition (ta, 3, symbol_q3_2, succ_q3);
  noll_uid_array_delete (succ_q3);

  /*
   * Transition: q3 -> [<next>, , m(next)](q9)
   *        -- start a list segment
   */
  const noll_ta_symbol_t *symbol_q3_3 =
    noll_ta_symbol_get_unique_allocated (sel_next, NULL, mark_next);
  assert (NULL != symbol_q3_3);
  succ_q3 = noll_uid_array_new ();
  noll_uid_array_push (succ_q3, 9);
  vata_add_transition (ta, 3, symbol_q3_3, succ_q3);
  noll_uid_array_delete (succ_q3);
  
  /*
   * Transition: q4 -> [,{fw},]()
   *        -- ref to forward var
   */
  const noll_ta_symbol_t *symbol_q4 =
    noll_ta_symbol_get_unique_aliased_var (fw_node);
  assert (NULL != symbol_q4);
  noll_uid_array *succ_empty = noll_uid_array_new ();
  vata_add_transition (ta, 4, symbol_q4, succ_empty);

  /*
   * Transition: q5 -> [,{pv},]()
   *        -- ref to prev var
   */
  const noll_ta_symbol_t *symbol_q5 =
    noll_ta_symbol_get_unique_aliased_var (pv_node);
  assert (NULL != symbol_q5);
  vata_add_transition (ta, 5, symbol_q5, succ_empty);

  /*
   * Transition: q6 -> [,s2(eps),]()
   *        -- ref to the input of the list
   * TODO: change as before when it is done one graph
   */
  const noll_ta_symbol_t *symbol_q6 =
    // noll_ta_symbol_get_unique_aliased_marking (2, mark_eps);
    noll_ta_symbol_get_unique_aliased_var(in_node);
  assert (NULL != symbol_q6);
  vata_add_transition (ta, 6, symbol_q6, succ_empty);
 
  /*
   * Transition: q7 -> [,s2(m(next)),]()
   *        -- ref to the previous inside the list
   */
  const noll_ta_symbol_t *symbol_q7 =
    noll_ta_symbol_get_unique_aliased_marking (2, mark_next);
  assert (NULL != symbol_q7);
  vata_add_transition (ta, 7, symbol_q7, succ_empty);
  noll_uid_array_delete(succ_empty);
  
  /*
   * Transition: q8 -> [<next>, , m(next)](q9)
   *        -- link by next to another dll cell
   */
  const noll_ta_symbol_t *symbol_q8_1 =
    noll_ta_symbol_get_unique_allocated (sel_next, NULL, mark_next);
  assert (NULL != symbol_q8_1);
  noll_uid_array *succ_q8 = noll_uid_array_new ();
  noll_uid_array_push (succ_q8, 9);
  vata_add_transition (ta, 8, symbol_q8_1, succ_q8);
  noll_uid_array_delete (succ_q8);

  /*
   * Transition: q8 -> [<next>, {out}, m(next)](q4)
   *        -- end of list segment dll
   */
  const noll_ta_symbol_t *symbol_q8_2 =
    noll_ta_symbol_get_unique_allocated (sel_next, vars_out, mark_next);
  assert (NULL != symbol_q8_2);
  succ_q8 = noll_uid_array_new ();
  noll_uid_array_push (succ_q8, 4);
  vata_add_transition (ta, 8, symbol_q8_2, succ_q8);
  noll_uid_array_delete (succ_q8);
 
  /*
   * Transition: q9 -> [<dll>, , m(next)](q8,q7)
   */
  const noll_ta_symbol_t *symbol_q9_1 =
    noll_ta_symbol_get_unique_higher_pred (pred, NULL, mark_next);
  assert (NULL != symbol_q9_1);
  noll_uid_array *succ_q9 = noll_uid_array_new ();
  noll_uid_array_push (succ_q9, 8);
  noll_uid_array_push (succ_q9, 7);
  vata_add_transition (ta, 9, symbol_q9_1, succ_q9);
  noll_uid_array_delete (succ_q9);

  /*
   * Transition: q9 -> [<next>, , m(next)](q3)
   */
  const noll_ta_symbol_t *symbol_q9_2 =
    noll_ta_symbol_get_unique_allocated (sel_next, NULL, mark_next);
  assert (NULL != symbol_q9_2);
  succ_q9 = noll_uid_array_new ();
  noll_uid_array_push (succ_q9, 3);
  vata_add_transition (ta, 9, symbol_q9_2, succ_q9);
  noll_uid_array_delete (succ_q9);

  noll_uid_array_delete (mark_eps);
  noll_uid_array_delete (mark_next);
  noll_uid_array_delete (vars_in);
  noll_uid_array_delete (vars_out);
  noll_uid_array_delete (vars_in_out);
  noll_uid_array_delete (sel_next);
  noll_uid_array_delete (sel_next_prev);
  noll_uid_array_delete (sel_prev);

  return ta;
}


uint_t noll_pred2ta_nll(noll_ta_t* ta, noll_pred_t* pred, 
           uid_t b_fid, uid_t z_fid, uid_t n_fid,
           uint_t qinit, 
           noll_uid_array* vars_in, noll_uid_array* mark_in,
           noll_uid_array* mark_out, unsigned char alias_out,
           noll_uid_array* mark_brd, unsigned char alias_brd);
           
/**
 * Get the TA for the edge built with predicate 'nll'
 * by instantiating the definition of the
 * 'nll(in, out, brd)' predicate (see ../samples/nll/nll-vc01.smt)
 *
 * nll(in,out,brd) = (in = out) or
 *                 (in != out and exists u,z. 
 *                       in -> {(s, u),(h, z)} * 
 *                       ls (z,brd) * nll(u,out,brd))
 * 
 * to the TA (q1 is a root state):
 * 
 * -- only simple fields --
 * q1 -> [<s,h>, {in}, [e]] (q2,q3)
 *       -- first cell
 * q2 -> [<s,h>, {}, [e::s]] (q2,qn)
 *       -- from cell two 
 * q2 -> [, {out}, ]()
 *       -- end
 * 
 * -- list segments --
 * q1 -> [<nll(brd)>, {in}, [e]] (q2)
 * q2 -> [<nll(brd)>, , [e::s]] (q2)
 * 
 * -- imported transitions --
 * k = ls(f, q3, {}, [e::h], {brd})
 * n = k+1
 *     ls(f, qn, {}, [e::s::h], {brd})
 */
noll_ta_t *
noll_edge2ta_nll (const noll_edge_t * edge)
{
  /* the checks on edge are done in the wrapper function */
  
  NOLL_DEBUG
    ("WARNING: Generating a fixed (and screwed-up) TA for the predicate nll\n");

  // get infos about the predicate 
  uint_t pid = edge->label;
  noll_pred_t *pred = noll_vector_at (preds_array, pid);
  assert (NULL != pred);

  /* find the fields main backbone, inner and nested for the nll predicate */
  uid_t b_fid = UNDEFINED_ID;
  uid_t z_fid = UNDEFINED_ID;
  uid_t n_fid = UNDEFINED_ID;
  assert (NULL != pred->typ->pfields);
  for (uint_t fid = 0; fid < noll_vector_size (fields_array); fid++) {
    noll_field_e k = noll_vector_at (pred->typ->pfields, fid);
    switch (k) {
      case NOLL_PFLD_BCKBONE:
      {
       assert (b_fid == UNDEFINED_ID);
       b_fid = fid;
       break;
      }
      case NOLL_PFLD_INNER:
      {
       assert (z_fid == UNDEFINED_ID);
       z_fid = fid;
       break;
      }
      case NOLL_PFLD_NESTED:
      {
       assert (n_fid == UNDEFINED_ID);
       n_fid = fid;
       break;
      }
      default:
      NOLL_DEBUG("Error: incorrect field for 'nll' predicate!\n");
      assert (false); 
    }
  }
  assert (UNDEFINED_ID != b_fid);
  assert (UNDEFINED_ID != z_fid);
  assert (UNDEFINED_ID != n_fid);
  
  /* build the TA */
  vata_ta_t *ta = NULL;
  if ((ta = vata_create_ta ()) == NULL)
    {
      return NULL;
    }
  vata_set_state_root (ta, 1);

  /* identifiers for arguments */
  uid_t in_node = noll_vector_at (edge->args, 0);
  uid_t end_node = noll_vector_at (edge->args, 1);
  uid_t brd_node = noll_vector_at (edge->args, 2);

  /* label of in variables */
  noll_uid_array *vars_in = noll_uid_array_new ();
  assert (NULL != vars_in);
  noll_uid_array_push (vars_in, in_node);

  /* label of out variables */
  noll_uid_array *vars_out = noll_uid_array_new ();
  assert (NULL != vars_out);
  noll_uid_array_push (vars_out, end_node);

  /* label of border variables */
  noll_uid_array *vars_brd = noll_uid_array_new ();
  assert (NULL != vars_brd);
  noll_uid_array_push (vars_brd, end_node);

  /* empty marking for first state, mark_eps = [eps] */
  noll_uid_array *mark_eps = noll_uid_array_new ();
  assert (NULL != mark_eps);
  noll_uid_array_push (mark_eps, NOLL_MARKINGS_EPSILON);

  uint_t qend = noll_pred2ta_nll(ta, pred, 
           b_fid, z_fid, n_fid, 1,
           vars_in, mark_eps, vars_out, 0, vars_brd, 0); 
           
  noll_uid_array_delete (vars_in);
  noll_uid_array_delete (vars_out);
  noll_uid_array_delete (vars_brd);
  noll_uid_array_delete (mark_eps);

  return ta;
}

 /**
 * Add to the @p ta the transitions encoding the nll predicate,
 * starting from state @p qinit, labeling the first state by @p vars_in,
 * ending in @p vars_out, and marking the first state by @p mark_in.
 * 
 * @param ta        the TA to which transitions are added
 * @param pred      the predicate generated
 * @param *_fid     the fields to be used as selector
 * @param qinit     the initial state to which transitions are added
 * @param vars_in   labeling of initial state
 * @param mark_in   marking of the initial state
 * @param mark_out  marking of output state
 * @param alias_out aliasing of the output state
 * @param mark_brd  marking of border state
 * @param alias_brd aliasing of the border state
 * @return          the number of the last state generated for @p ta
 */
uint_t 
noll_pred2ta_nll(noll_ta_t* ta, noll_pred_t* pred, 
           uid_t b_fid, uid_t z_fid, uid_t n_fid,
           uint_t qinit, 
           noll_uid_array* vars_in, noll_uid_array* mark_in,
           noll_uid_array* mark_out, unsigned char alias_out,
           noll_uid_array* mark_brd, unsigned char alias_brd)
{
    
  NOLL_DEBUG
    ("WARNING: Generating a nested TA for the predicate nll\n");

  assert (NULL != ta);
  assert (NULL != mark_in); // at least eps
  assert (NULL != mark_out); // at least one marking
  assert (noll_vector_size(mark_out) >= 1);
  assert (NULL != mark_brd); // at least one marking
  assert (noll_vector_size(mark_brd) >= 1);
 
  /* nested predicate ls */
  noll_pred_t* pred_ls = NULL;
  for (uint_t pid = 0; pid < noll_vector_size (preds_array); pid++) 
    if (noll_vector_at (pred->typ->ppreds, pid) == 1)
       pred_ls = noll_vector_at(preds_array,pid);
  assert (NULL != pred_ls);
 
  /* states of the automaton */
  uint_t q1 = qinit; // initial cell
  uint_t q2 = qinit + 1; // inner cells
  uint_t q3 = qinit + 2; // nested ls from init cell
  uint_t q4 = UNDEFINED_ID; // nested ls from inner cells, computed
  uint_t qlast = UNDEFINED_ID; // last state used in the inner automaton ls
 
  /* the selectors <b_fid, z_fid> */
  noll_uid_array *selectors = noll_uid_array_new ();
  assert (NULL != selectors);
  noll_uid_array_push (selectors, b_fid);
  noll_uid_array_push (selectors, z_fid);

  /* the marking used mark_in_bkb = mark_in . b_fid */
  noll_uid_array *mark_in_bkb = noll_uid_array_new ();
  assert (NULL != mark_in_bkb);
  noll_uid_array_copy (mark_in_bkb, mark_in);
  noll_uid_array_push (mark_in_bkb, b_fid);

  /* the marking used mark_in_z = mark_in . z_fid */
  noll_uid_array *mark_in_z = noll_uid_array_new ();
  assert (NULL != mark_in_z);
  noll_uid_array_copy (mark_in_z, mark_in);
  noll_uid_array_push (mark_in_z, z_fid);

  /* the marking used mark_in_bkb_z = mark_in_bkb . z_fid */
  noll_uid_array *mark_in_bkb_z = noll_uid_array_new ();
  assert (NULL != mark_in_bkb_z);
  noll_uid_array_copy (mark_in_bkb_z, mark_in_bkb);
  noll_uid_array_push (mark_in_bkb_z, z_fid);

  /*
   * Transition: q1 -> [<s,h>, {in}, [e]] (q2,q3)
   *       -- first cell
   */
  const noll_ta_symbol_t *symbol_q1_1 =
    noll_ta_symbol_get_unique_allocated (selectors, vars_in, mark_in);
  assert (NULL != symbol_q1_1);
  noll_uid_array* succ_q1 = noll_uid_array_new ();
  noll_uid_array_push (succ_q1, q2);
  noll_uid_array_push (succ_q1, q3);
  vata_add_transition (ta, q1, symbol_q1_1, succ_q1);
  noll_uid_array_delete (succ_q1);
  
  /*
   * Transition: q1 -> [<nll(brd)>, {in}, [e]] (q2)
   *       -- list segment from q1
   */
  const noll_ta_symbol_t *symbol_q1_2 =
    noll_ta_symbol_get_unique_higher_pred (pred, mark_brd, mark_in);
    // TODO: see if {in} can be added
  assert (NULL != symbol_q1_2);
  succ_q1 = noll_uid_array_new ();
  noll_uid_array_push (succ_q1, q2);
  vata_add_transition (ta, q1, symbol_q1_2, succ_q1);
  noll_uid_array_delete (succ_q1);

  /*
   * Transitions: k = ls(f, q3, {}, [e::h], {brd})
   */
  q4 = noll_pred2ta_ls(ta, pred_ls, n_fid, q3, NULL, mark_in_z, mark_brd, alias_brd);
  assert (UNDEFINED_ID != q4);
  assert (q4 > q3);
  
  q4 += 1; // next state free
   
   /*
    * Transition: q2 -> [, {out}, ]()
    *       -- end
    */
  const noll_ta_symbol_t *symbol_q2_1 = NULL;
  if (alias_out == 0) 
    symbol_q2_1 = noll_ta_symbol_get_unique_aliased_var (noll_vector_at(mark_out,0));
  else
    symbol_q2_1 = noll_ta_symbol_get_unique_aliased_marking (alias_out, mark_out);
  assert (NULL != symbol_q2_1);
  noll_uid_array* succ_q2 = noll_uid_array_new ();
  vata_add_transition (ta, q2, symbol_q2_1, succ_q2);
  
  /*
   * Transition: q2 -> [<nll(brd)>, , [e::s]] (q2)
   *       -- inner list segment
   */
  const noll_ta_symbol_t *symbol_q2_2 =
    noll_ta_symbol_get_unique_higher_pred (pred, mark_brd, mark_in);
    // TODO: see if {in} can be added
  assert (NULL != symbol_q2_2);
  assert (succ_q2 != NULL);
  noll_uid_array_push (succ_q2, q2);
  vata_add_transition (ta, q2, symbol_q2_2, succ_q2);
  // succ_q2 used below 
  
  /*
   * Transition: q2 -> [<s,h>, {}, [e::s]] (q2,q4)
   *       -- from cell two
   */
  const noll_ta_symbol_t *symbol_q2_3 =
    noll_ta_symbol_get_unique_allocated (selectors, NULL, mark_in_bkb);
  assert (NULL != symbol_q2_3);
  // succ_q2 = [q2]
  noll_uid_array_push (succ_q2, q4);
  vata_add_transition (ta, q2, symbol_q2_3, succ_q2);
  noll_uid_array_delete (succ_q2);
  
  /*
   * Transitions: ls(f, qn, {}, [e::s::h], {brd})
   *       -- nested list segment
   */
  qlast = noll_pred2ta_ls(ta, pred_ls, n_fid, q4, NULL, mark_in_bkb_z, mark_brd, alias_brd);
  assert (UNDEFINED_ID != qlast);
  assert (qlast > q4);
  
  noll_uid_array_delete(mark_in_bkb);
  noll_uid_array_delete(mark_in_z);
  noll_uid_array_delete(mark_in_bkb_z);
  noll_uid_array_delete(selectors);
  
  return qlast;
}

uint_t noll_pred2ta_nlcl(noll_ta_t* ta, noll_pred_t* pred, 
           uid_t b_fid, uid_t z_fid, uid_t n_fid,
           uint_t qinit, 
           noll_uid_array* vars_in, noll_uid_array* mark_in,
           noll_uid_array* mark_out, unsigned char alias_out);
           
/**
 * Get the TA for the edge built with predicate 'nlcl'
 * by instantiating the definition of the
 * 'nlcl(in, out)' predicate (see ../samples/nll/nlcl-vc01.smt)
 *
 * nlcl(in,out) = (in = out) or
 *                (in != out and exists u,z. 
 *                       in -> {(s, u),(h, z)} * 
 *                       loop (ls (z,z)) * nlcl(u,out))
 * 
 * to the TA (q1 is a root state):
 * 
 * -- only simple fields --
 * q1 -> [<s,h>, {in}, [e]] (q2,q3)
 *       -- first cell
 * q2 -> [<s,h>, {}, [e::s]] (q2,qn)
 *       -- from cell two 
 * q2 -> [, {out}, ]()
 *       -- end
 * 
 * -- list segments --
 * q1 -> [<nlcl>, {in}, [e]] (q2)
 * q2 -> [<nlcl>, , [e::s]] (q2)
 * 
 * -- imported transitions --
 * k = ls(f, q3, {}, [e::h], s1[e::h])
 * n = k+1
 *     ls(f, qn, {}, [e::s::h], s1[e::s::h])
 */
noll_ta_t *
noll_edge2ta_nlcl (const noll_edge_t * edge)
{
  /* the checks on edge are done in the wrapper function */
  
  NOLL_DEBUG
    ("WARNING: Generating a fixed (and screwed-up) TA for the predicate nlcl\n");

  // get infos about the predicate 
  uint_t pid = edge->label;
  noll_pred_t *pred = noll_vector_at (preds_array, pid);
  assert (NULL != pred);

  /* find the fields main backbone, inner and nested for the nlcl predicate */
  uid_t b_fid = UNDEFINED_ID;
  uid_t z_fid = UNDEFINED_ID;
  uid_t n_fid = UNDEFINED_ID;
  assert (NULL != pred->typ->pfields);
  for (uint_t fid = 0; fid < noll_vector_size (fields_array); fid++) {
    noll_field_e k = noll_vector_at (pred->typ->pfields, fid);
    switch (k) {
      case NOLL_PFLD_BCKBONE:
      {
       assert (b_fid == UNDEFINED_ID);
       b_fid = fid;
       break;
      }
      case NOLL_PFLD_INNER:
      {
       assert (z_fid == UNDEFINED_ID);
       z_fid = fid;
       break;
      }
      case NOLL_PFLD_NESTED:
      {
       assert (n_fid == UNDEFINED_ID);
       n_fid = fid;
       break;
      }
      default:
      NOLL_DEBUG("Error: incorrect field for 'nll' predicate!\n");
      assert (false); 
    }
  }
  assert (UNDEFINED_ID != b_fid);
  assert (UNDEFINED_ID != z_fid);
  assert (UNDEFINED_ID != n_fid);
  
  /* build the TA */
  vata_ta_t *ta = NULL;
  if ((ta = vata_create_ta ()) == NULL)
    {
      return NULL;
    }
  vata_set_state_root (ta, 1);

  /* identifiers for arguments */
  uid_t in_node = noll_vector_at (edge->args, 0);
  uid_t end_node = noll_vector_at (edge->args, 1);

  /* label of in variables */
  noll_uid_array *vars_in = noll_uid_array_new ();
  assert (NULL != vars_in);
  noll_uid_array_push (vars_in, in_node);

  /* label of out variables */
  noll_uid_array *vars_out = noll_uid_array_new ();
  assert (NULL != vars_out);
  noll_uid_array_push (vars_out, end_node);

  /* empty marking for first state, mark_eps = [eps] */
  noll_uid_array *mark_eps = noll_uid_array_new ();
  assert (NULL != mark_eps);
  noll_uid_array_push (mark_eps, NOLL_MARKINGS_EPSILON);

  uint_t qend = noll_pred2ta_nlcl(ta, pred, 
           b_fid, z_fid, n_fid, 1,
           vars_in, mark_eps, vars_out, 0); 
           
  noll_uid_array_delete (vars_in);
  noll_uid_array_delete (vars_out);
  noll_uid_array_delete (mark_eps);

  return ta;
}

 /**
 * Add to the @p ta the transitions encoding the nlcl predicate,
 * starting from state @p qinit, labeling the first state by @p vars_in,
 * ending in @p vars_out, and marking the first state by @p mark_in.
 * 
 * @param ta        the TA to which transitions are added
 * @param pred      the predicate generated
 * @param *_fid     the fields to be used as selector
 * @param qinit     the initial state to which transitions are added
 * @param vars_in   labeling of initial state
 * @param mark_in   marking of the initial state
 * @param mark_out  marking of output state
 * @param alias_out aliasing of the output state
 * @return          the number of the last state generated for @p ta
 */
uint_t 
noll_pred2ta_nlcl(noll_ta_t* ta, noll_pred_t* pred, 
           uid_t b_fid, uid_t z_fid, uid_t n_fid,
           uint_t qinit, 
           noll_uid_array* vars_in, noll_uid_array* mark_in,
           noll_uid_array* mark_out, unsigned char alias_out)
{
    
  NOLL_DEBUG
    ("WARNING: Generating a nested TA for the predicate nlcl\n");

  assert (NULL != ta);
  assert (NULL != mark_in); // at least eps
  assert (NULL != mark_out); // at least one marking
  assert (noll_vector_size(mark_out) >= 1);
 
  /* nested predicate ls */
  noll_pred_t* pred_ls = NULL;
  for (uint_t pid = 0; pid < noll_vector_size (preds_array); pid++) 
    if (noll_vector_at (pred->typ->ppreds, pid) == 1)
       pred_ls = noll_vector_at(preds_array,pid);
  assert (NULL != pred_ls);
 
  /* states of the automaton */
  uint_t q1 = qinit; // initial cell
  uint_t q2 = qinit + 1; // inner cells
  uint_t q3 = qinit + 2; // nested ls from init cell
  uint_t q4 = UNDEFINED_ID; // nested ls from inner cells, computed
  uint_t qlast = UNDEFINED_ID; // last state used in the inner automaton ls
 
  /* the selectors <b_fid, z_fid> */
  noll_uid_array *selectors = noll_uid_array_new ();
  assert (NULL != selectors);
  noll_uid_array_push (selectors, b_fid);
  noll_uid_array_push (selectors, z_fid);

  /* the marking used mark_in_bkb = mark_in . b_fid */
  noll_uid_array *mark_in_bkb = noll_uid_array_new ();
  assert (NULL != mark_in_bkb);
  noll_uid_array_copy (mark_in_bkb, mark_in);
  noll_uid_array_push (mark_in_bkb, b_fid);

  /* the marking used mark_in_z = mark_in . z_fid */
  noll_uid_array *mark_in_z = noll_uid_array_new ();
  assert (NULL != mark_in_z);
  noll_uid_array_copy (mark_in_z, mark_in);
  noll_uid_array_push (mark_in_z, z_fid);

  /* the marking used mark_in_bkb_z = mark_in_bkb . z_fid */
  noll_uid_array *mark_in_bkb_z = noll_uid_array_new ();
  assert (NULL != mark_in_bkb_z);
  noll_uid_array_copy (mark_in_bkb_z, mark_in_bkb);
  noll_uid_array_push (mark_in_bkb_z, z_fid);

  /*
   * Transition: q1 -> [<s,h>, {in}, [e]] (q2,q3)
   *       -- first cell
   */
  const noll_ta_symbol_t *symbol_q1_1 =
    noll_ta_symbol_get_unique_allocated (selectors, vars_in, mark_in);
  assert (NULL != symbol_q1_1);
  noll_uid_array* succ_q1 = noll_uid_array_new ();
  noll_uid_array_push (succ_q1, q2);
  noll_uid_array_push (succ_q1, q3);
  vata_add_transition (ta, q1, symbol_q1_1, succ_q1);
  noll_uid_array_delete (succ_q1);
  
  /*
   * Transition: q1 -> [<nlcl>, {in}, [e]] (q2)
   *       -- list segment from q1
   */
  const noll_ta_symbol_t *symbol_q1_2 =
    noll_ta_symbol_get_unique_higher_pred (pred, NULL, mark_in);
    // TODO: see if {in} can be added
  assert (NULL != symbol_q1_2);
  succ_q1 = noll_uid_array_new ();
  noll_uid_array_push (succ_q1, q2);
  vata_add_transition (ta, q1, symbol_q1_2, succ_q1);
  noll_uid_array_delete (succ_q1);

  /*
   * Transitions: k = ls(f, q3, {}, [e::h], s1[e::h])
   */
  q4 = noll_pred2ta_ls(ta, pred_ls, n_fid, q3, NULL, mark_in_z, mark_in_z, 1);
  assert (UNDEFINED_ID != q4);
  assert (q4 > q3);
  
  q4 += 1; // next state free
   
   /*
    * Transition: q2 -> [, {out}, ]()
    *       -- end
    */
  const noll_ta_symbol_t *symbol_q2_1 = NULL;
  if (alias_out == 0) 
    symbol_q2_1 = noll_ta_symbol_get_unique_aliased_var (noll_vector_at(mark_out,0));
  else
    symbol_q2_1 = noll_ta_symbol_get_unique_aliased_marking (alias_out, mark_out);
  assert (NULL != symbol_q2_1);
  noll_uid_array* succ_q2 = noll_uid_array_new ();
  vata_add_transition (ta, q2, symbol_q2_1, succ_q2);
  
  /*
   * Transition: q2 -> [<nlcl>, , [e::s]] (q2)
   *       -- inner list segment
   */
  const noll_ta_symbol_t *symbol_q2_2 =
    noll_ta_symbol_get_unique_higher_pred (pred, NULL, mark_in);
    // TODO: see if {in} can be added
  assert (NULL != symbol_q2_2);
  assert (succ_q2 != NULL);
  noll_uid_array_push (succ_q2, q2);
  vata_add_transition (ta, q2, symbol_q2_2, succ_q2);
  // succ_q2 used below 
  
  /*
   * Transition: q2 -> [<s,h>, {}, [e::s]] (q2,q4)
   *       -- from cell two
   */
  const noll_ta_symbol_t *symbol_q2_3 =
    noll_ta_symbol_get_unique_allocated (selectors, NULL, mark_in_bkb);
  assert (NULL != symbol_q2_3);
  // succ_q2 = [q2]
  noll_uid_array_push (succ_q2, q4);
  vata_add_transition (ta, q2, symbol_q2_3, succ_q2);
  noll_uid_array_delete (succ_q2);
  
  /*
   * Transitions: ls(f, q4, {}, [e::s::h], s1([e::s::h])
   *       -- nested list segment
   */
  qlast = noll_pred2ta_ls(ta, pred_ls, n_fid, q4, NULL, mark_in_bkb_z, mark_in_bkb_z, 1);
  assert (UNDEFINED_ID != qlast);
  assert (qlast > q4);
  
  noll_uid_array_delete(mark_in_bkb);
  noll_uid_array_delete(mark_in_z);
  noll_uid_array_delete(mark_in_bkb_z);
  noll_uid_array_delete(selectors);
  
  return qlast;
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
  else if (0 == strcmp (pred->pname, "nlcl"))
    {
      ta = noll_edge2ta_nlcl (edge);
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
