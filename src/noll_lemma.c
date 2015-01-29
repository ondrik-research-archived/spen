/**************************************************************************
 *
 *  SPEN decision procedure
 *
 *  you can redistribute it and/or modify it under the terms of the GNU
 *  Lesser General Public License as published by the Free Software
 *  Foundation, version 3.
 *
 *  It is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU Lesser General Public License for more details.
 *
 *  See the GNU Lesser General Public License version 3.
 *  for more details (enclosed in the file LICENSE).
 *
 **************************************************************************/

/**
 * Lemma representation and checking for the syntactic procedure.
 */

#include <stdbool.h>
#include "noll_lemma.h"
#include "noll.h"               // for NOLL_DEBUG

NOLL_VECTOR_DEFINE (noll_lemma_array, noll_lemma_t *);

/* ====================================================================== */
/* Globals */
/* ====================================================================== */

noll_lemma_array **lemma_array;

noll_lemma_array *noll_lemma_init_pred (uint_t pid);

/**
 * @brief Allocates the global array of lemma and initialize it.
 */
void
noll_lemma_init (void)
{
  assert (preds_array != NULL && noll_vector_size (preds_array) > 0);

  uint_t size = noll_vector_size (preds_array);
  lemma_array =
    (noll_lemma_array **) malloc (sizeof (noll_lemma_array *) * size);
  for (uint_t pid = 0; pid < size; pid++)
    lemma_array[pid] = noll_lemma_init_pred (pid);
}

/* ====================================================================== */
/* Constructors/Destructors */
/* ====================================================================== */

/**
 * @brief Return an empty lemma for predicate @p pid.
 */
noll_lemma_t *
noll_lemma_new (uint_t pid)
{
  const noll_pred_t *pred = noll_pred_getpred (pid);
  noll_lemma_t *lem = (noll_lemma_t *) malloc (sizeof (noll_lemma_t));
  lem->pid = pid;
  lem->rule.vars = noll_var_array_new ();
  noll_var_array_copy (lem->rule.vars, pred->def->vars);
  lem->rule.fargs = pred->def->fargs;
  lem->rule.pure = NULL;
  lem->rule.pto = NULL;
  lem->rule.nst = NULL;
  lem->rule.rec = NULL;
  return lem;
}

/**
 * @brief Adds to (a copy of) @p bvars, the variables in @p pvars.
 */
void
noll_lemma_add_lvars (noll_lemma_t * lem,
                      noll_var_array * bvars, noll_var_array * pvars)
{
  assert (lem != NULL);

  /// copy @p bvars
  lem->rule.vars = noll_var_array_new ();
  noll_var_array_copy (lem->rule.vars, bvars);

  /// get from @p pvars variables of different type
  uint_t bvars_len = noll_vector_size (bvars);
  uint_t pvars_len = noll_vector_size (pvars);
  uint_t bi = 0;
  uint_t pi = 0;
  while ((bi < bvars_len) && (pi < pvars_len))
    {
      /// check the type
      noll_type_t *typ_bi = noll_var_type (bvars, bi);
      noll_type_t *typ_pi = noll_var_type (pvars, pi);
      assert (typ_bi != NULL);
      assert (typ_pi != NULL);
      if (typ_bi->kind != typ_pi->kind) // TODO: does not work if border!
        {
          // push the variable at pi
          noll_var_t *vi = noll_var_copy (noll_vector_at (pvars, pi));
          char *nname =
            (char *) malloc (sizeof (char) * (strlen (vi->vname) + 3));
          snprintf (nname, strlen (vi->vname) + 3, "%s_%d", vi->vname, pi);     // TODO: be more robust
          free (vi->vname);
          vi->vname = nname;
          noll_var_array_push (lem->rule.vars, vi);
          pi++;
        }
      else
        {
          bi++;
          pi++;
        }
    }
}


/**
 * @brief Adds to (a copy of) @p pvars, the destination vars in @p pvars.
 */
void
noll_lemma_clone_lvars (noll_lemma_t * lem, noll_var_array * pvars)
{
  assert (lem != NULL);

  /// copy @p bvars
  lem->rule.vars = noll_var_array_new ();
  noll_var_array_copy (lem->rule.vars, pvars);

  uint_t pvars_len = noll_vector_size (pvars);
  for (uint_t pi = 2; pi < pvars_len; pi++)
    {
      // push the variable at pi
      noll_var_t *vi = noll_var_copy (noll_vector_at (pvars, pi));
      char *nname =
        (char *) malloc (sizeof (char) * (strlen (vi->vname) + 3));
      snprintf (nname, strlen (vi->vname) + 3, "%s_%d", vi->vname, pi); // TODO: be more robust
      free (vi->vname);
      vi->vname = nname;
      noll_var_array_push (lem->rule.vars, vi);
      pi += 2;                  // TODO: does not work for predicates with border args
    }
}

/**
 * @brief Build the lemma for
 *  @p pid_part(E,r1,B,M,b1,d1,d) /\ r1=nil /\ M=emptybag /\ d1=0 
 *        => @p pid_base(E,M,B,d)
 */
noll_lemma_t *
noll_lemma_new_spec_nil (uid_t pid_base, uid_t pid_part)
{
  assert (pid_base != UNDEFINED_ID);
  assert (pid_part != UNDEFINED_ID);

  const noll_pred_t *pred_base = noll_pred_getpred (pid_base);
  const noll_pred_t *pred_part = noll_pred_getpred (pid_part);

  noll_lemma_t *lem1 = noll_lemma_new (pid_base);
  // adds to pred_base->def->vars the additional parameters of pred_part->def->vars
  noll_lemma_add_lvars (lem1, pred_base->def->vars, pred_part->def->vars);
  lem1->rule.pure = noll_pure_new (noll_vector_size (lem1->rule.vars));
  uint_t fargs_base = pred_base->def->fargs;
  uint_t fargs_part = pred_part->def->fargs;
  assert ((fargs_base + 1) <= fargs_part);
  // push (always) r1 (id fargs_base) = nil (id 0)
  noll_pure_add_eq (lem1->rule.pure, fargs_base + 1, 0);
  // push equalities for the other parameters
  for (uint_t i = fargs_base + 2; i <= fargs_part; i++) // TODO: <=fargs_part for nil?
    {
      noll_type_t *typ_vi = noll_var_type (lem1->rule.vars, i);
      assert (typ_vi != NULL);
      noll_dform_t *df = noll_dform_new ();
      if (typ_vi->kind == NOLL_TYP_BAGINT)
        {                       // push b1 = emptybag
          noll_dterm_t *dt_b1 = noll_dterm_new ();
          dt_b1->kind = NOLL_DATA_VAR;
          dt_b1->typ = NOLL_TYP_BAGINT;
          dt_b1->p.sid = i;
          noll_dterm_t *dt_eb = noll_dterm_new ();
          dt_b1->kind = NOLL_DATA_EMPTYBAG;
          dt_b1->typ = NOLL_TYP_BAGINT;
          df = noll_dform_new ();
          df->kind = NOLL_DATA_EQ;
          df->kind = NOLL_TYP_BAGINT;
          if (df->p.targs == NULL)
            df->p.targs = noll_dterm_array_new ();
          noll_dterm_array_push (df->p.targs, dt_b1);
          noll_dterm_array_push (df->p.targs, dt_eb);
          noll_pure_add_dform (lem1->rule.pure, df);

        }
      else if (typ_vi->kind == NOLL_TYP_INT)
        {                       // push i1 = 0
          noll_dterm_t *dt_i1 = noll_dterm_new ();
          dt_i1->kind = NOLL_DATA_VAR;
          dt_i1->typ = NOLL_TYP_INT;
          dt_i1->p.sid = i;
          noll_dterm_t *dt_0 = noll_dterm_new ();
          dt_0->kind = NOLL_DATA_INT;
          dt_0->typ = NOLL_TYP_INT;
          dt_0->p.value = 0l;
          df = noll_dform_new ();
          df->kind = NOLL_DATA_EQ;
          df->kind = NOLL_TYP_INT;
          if (df->p.targs == NULL)
            df->p.targs = noll_dterm_array_new ();
          noll_dterm_array_push (df->p.targs, dt_i1);
          noll_dterm_array_push (df->p.targs, dt_0);
          noll_pure_add_dform (lem1->rule.pure, df);
        }
      else
        {
          NOLL_DEBUG
            ("lemma_spec_nil: incorrect type of the additional parameter");
        }
    }
  // push pred_part(E,r1,M,b1,...)
  noll_space_t *nst = noll_space_new ();
  nst->kind = NOLL_SPACE_LS;
  nst->is_precise = true;
  nst->m.ls.pid = pid_part;
  assert (nst->m.ls.pid != UNDEFINED_ID);
  nst->m.ls.is_loop = false;
  nst->m.ls.sid = UNDEFINED_ID;
  nst->m.ls.args = noll_uid_array_new ();
  // copy source and border but 
  // change the other "destination" parameters, if any
  for (uint_t pos = 1; pos <= fargs_part; pos++)
    {                           // TODO: do not work when border refs are present
      if ((pos % 2) == 0)
        noll_uid_array_push (nst->m.ls.args, fargs_base + (pos / 2));
      else
        noll_uid_array_push (nst->m.ls.args, pos);
    }
  lem1->rule.nst = nst;

  return lem1;

}

/**
 * @brief Build the lemma for
 *  @p pid(E,E',B,M,M',d,d',dB) * @p pid(E',F,B,M',N,d',z,dB) 
 *        => @p pid(E,F,B,M,N,d,z,dB)
 */
noll_lemma_t *
noll_lemma_new_comp_1 (uid_t pid)
{
  assert (pid != UNDEFINED_ID);

  const noll_pred_t *pred = noll_pred_getpred (pid);
  uint_t fargs = pred->def->fargs;

  noll_lemma_t *lem2 = noll_lemma_new (pid);
  // adds to pred->def->vars the copy of the "destination" parameters
  noll_lemma_clone_lvars (lem2, pred->def->vars);
  uint_t largs = noll_vector_size (lem2->rule.vars);
  lem2->rule.pure = NULL;       // no constraint
  lem2->rule.nst = NULL;        // no constraint
  noll_space_t *rec2 = noll_space_new ();
  rec2->kind = NOLL_SPACE_SSEP;
  rec2->is_precise = true;
  rec2->m.sep = noll_space_array_new ();
  noll_space_array_reserve (rec2->m.sep, 2);

  // push pred(E,E',B,M,M',d,d',dB) in the "recursive" part
  noll_space_t *call1 = noll_space_new ();
  call1->kind = NOLL_SPACE_LS;
  call1->is_precise = true;
  call1->m.ls.pid = pid;
  assert (call1->m.ls.pid != UNDEFINED_ID);
  call1->m.ls.is_loop = false;
  call1->m.ls.sid = UNDEFINED_ID;
  call1->m.ls.args = noll_uid_array_new ();
  // copy source and border but 
  // change the other "destination" parameters, if any
  for (uint_t pos = 1; pos < largs; pos++)
    {                           // TODO: do not work when border refs are present
      if ((pos % 2) == 0)
        noll_uid_array_push (call1->m.ls.args, fargs + (pos / 2));
      else
        noll_uid_array_push (call1->m.ls.args, pos);
    }
  noll_space_array_push (rec2->m.sep, call1);

  // push pred(E',F,B,M',N,d',z,dB)) in the "recursive" part
  noll_space_t *call2 = noll_space_new ();
  call2->kind = NOLL_SPACE_LS;
  call2->is_precise = true;
  call2->m.ls.pid = pid;
  assert (call2->m.ls.pid != UNDEFINED_ID);
  call2->m.ls.is_loop = false;
  call2->m.ls.sid = UNDEFINED_ID;
  call2->m.ls.args = noll_uid_array_new ();
  // copy destination and border but 
  // change the "source" parameters
  for (uint_t pos = 1; pos < largs; pos++)
    {                           // TODO: do not work when border refs are present
      if ((pos % 2) == 0)
        noll_uid_array_push (call2->m.ls.args, pos);
      else
        noll_uid_array_push (call1->m.ls.args, fargs + (pos / 2));
    }
  noll_space_array_push (rec2->m.sep, call2);

  return lem2;
}

/**
 * @brief Build the lemma for
 *  @p pid_part(E,r1,B,M,b1,d1,d) * @pid_base (r1,b1,d1,d) 
 *        => @p pid_base(E,M,B,d)
 */
noll_lemma_t *
noll_lemma_new_comp_2 (uid_t pid_base, uid_t pid_part)
{
  assert (pid_base != UNDEFINED_ID);
  assert (pid_part != UNDEFINED_ID);

  const noll_pred_t *pred_base = noll_pred_getpred (pid_base);
  const noll_pred_t *pred_part = noll_pred_getpred (pid_part);

  noll_lemma_t *lem2 = noll_lemma_new (pid_base);
  // adds to pred_base->def->vars the additional parameters of pred_part->def->vars
  noll_lemma_add_lvars (lem2, pred_base->def->vars, pred_part->def->vars);
  lem2->rule.pure = NULL;       // no constraint
  uint_t fargs_base = pred_base->def->fargs;
  uint_t fargs_part = pred_part->def->fargs;
  assert ((fargs_base + 1) <= fargs_part);

  // push pred_part(E,r1,M,b1) in the "nested" part
  noll_space_t *nst2 = noll_space_new ();
  nst2->kind = NOLL_SPACE_LS;
  nst2->is_precise = true;
  nst2->m.ls.pid = pid_part;
  assert (nst2->m.ls.pid != UNDEFINED_ID);
  nst2->m.ls.is_loop = false;
  nst2->m.ls.sid = UNDEFINED_ID;
  nst2->m.ls.args = noll_uid_array_new ();
  // copy source and border but 
  // change the other "destination" parameters, if any
  for (uint_t pos = 1; pos <= fargs_part; pos++)
    {                           // TODO: do not work when border refs are present
      if ((pos % 2) == 0)
        noll_uid_array_push (nst2->m.ls.args, fargs_base + (pos / 2));
      else
        noll_uid_array_push (nst2->m.ls.args, pos);
    }
  lem2->rule.nst = nst2;

  // push pred(r1,b1) in the "recursive" part
  noll_space_t *rec2 = noll_space_new ();
  rec2->kind = NOLL_SPACE_LS;
  rec2->is_precise = true;
  rec2->m.ls.pid = pid_base;
  assert (rec2->m.ls.pid != UNDEFINED_ID);
  rec2->m.ls.is_loop = false;
  rec2->m.ls.sid = UNDEFINED_ID;
  rec2->m.ls.args = noll_uid_array_new ();
  // change the source arguments
  for (uint_t i = fargs_base + 1; i <= fargs_part; i++) // TODO: <=fargs_part for nil?
    {
      noll_uid_array_push (rec2->m.ls.args, i);
    }
  lem2->rule.rec = rec2;
  return lem2;
}

/**
 * @brief Return the set of lemma for the predicate bst.
 */
noll_lemma_array *
noll_lemma_init_bst (uint_t pid)
{
  noll_lemma_array *res = noll_lemma_array_new ();
  noll_lemma_array_reserve (res, 2);

  // TODO: find the "partial" RD of pid using typing
  uid_t pid_bsth = noll_pred_array_find ("bsthole");
  assert (pid_bsth != UNDEFINED_ID);

  /// first lemma:
  ///   bsthole(E,r1,M,b1) /\ r1=nil /\ b1=emptybag => bst(E,M)
  noll_lemma_t *lem1 = noll_lemma_new_spec_nil (pid, pid_bsth);
  // push lemma
  noll_lemma_array_push (res, lem1);

  /// second lemma:
  ///   bsthole(E,r1,M,b1) * bst(r1,b1) => bst(E,M)
  noll_lemma_t *lem2 = noll_lemma_new_comp_2 (pid, pid_bsth);
  // push lemma
  noll_lemma_array_push (res, lem2);

  return res;
}

/**
 * @brief Return the set of lemma for the predicate bsth(ole).
 */
noll_lemma_array *
noll_lemma_init_bsthole (uint_t pid)
{
  uid_t pid_bst = noll_pred_array_find ("bst");
  assert (pid_bst != UNDEFINED_ID);

  noll_lemma_array *res = noll_lemma_array_new ();
  noll_lemma_array_reserve (res, 1);

  /// generate composition lemma for bsthole
  noll_lemma_t *lem = noll_lemma_new_comp_1 (pid);
  // push lemma
  noll_lemma_array_push (res, lem);
  return res;
}

/**
 * @brief Return the set of lemma for the predicate @p pid.
 */
noll_lemma_array *
noll_lemma_init_pred (uint_t pid)
{
  assert (pid != UNDEFINED_ID);

  const char *pname = noll_pred_name (pid);

  // TODO: test some condition computed by typing instead of the below one
  if (strncmp (pname, "bsth", 4) == 0)
    return noll_lemma_init_bsthole (pid);

  if (strncmp (pname, "bst", 3) == 0)
    return noll_lemma_init_bst (pid);

  // TODO: fill with lemma for other predicates
  return NULL;
}


  /* ====================================================================== */
  /* Printing */
  /* ====================================================================== */

/**
 * @brief Print the global array of lemmas.
 */
void
noll_lemma_array_fprint (FILE * f)
{
  assert (f != NULL);

  if (lemma_array == NULL)
    {
      fprintf (f, "(lemma_array) []");
      return;
    }
  for (uint_t pi = 0; pi < noll_vector_size (preds_array); pi++)
    {
      fprintf (f, "%s -> [", noll_pred_name (pi));
      noll_lemma_array *lem_pid = lemma_array[pi];
      if (lem_pid != NULL)
        {
          for (uint_t li = 0; li < noll_vector_size (lem_pid); li++)
            {
              noll_lemma_fprint (f, noll_vector_at (lem_pid, li));
              fprintf (f, "\n");
            }
        }
      fprintf (f, "\t]\n");
    }
}

void
noll_lemma_fprint (FILE * f, noll_lemma_t * l)
{
  assert (NULL != f);

  if (l == NULL)
    {
      fprintf (f, "(lemma) []");
      return;
    }
  const noll_pred_t *prhs = noll_pred_getpred (l->pid);

  if (l->rule.pure != NULL)
    {
      noll_pure_fprint (f, l->rule.vars, l->rule.pure);
      fprintf (f, " & \n");
    }
  if (l->rule.nst != NULL)
    {
      noll_space_fprint (f, l->rule.vars, NULL, l->rule.nst);
      fprintf (f, " * \n");
    }
  if (l->rule.rec != NULL)
    {
      noll_space_fprint (f, l->rule.vars, NULL, l->rule.rec);
    }
}
