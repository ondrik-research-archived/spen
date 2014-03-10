/**************************************************************************/
/*                                                                        */
/*  NOLL decision procedure                                               */
/*                                                                        */
/*  Copyright (C) 2012                                                    */
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
 * Predicates for NOLL.
 */

#include "noll_preds.h"

NOLL_VECTOR_DEFINE (noll_pred_array, noll_pred_t *);

/* ====================================================================== */
/* Globals */
/* ====================================================================== */

noll_pred_array *preds_array;

void
noll_pred_init ()
{
  preds_array = noll_pred_array_new ();
  noll_pred_array_reserve (preds_array, 4);
}

/* ====================================================================== */
/* Other methods */
/* ====================================================================== */

noll_pred_t *
noll_pred_new (const char *name, uid_t pid, noll_pred_binding_t * def)
{
  noll_pred_t *p = (noll_pred_t *) malloc (sizeof (struct noll_pred_t));
  p->pname = strdup (name);
  p->pid = pid;
  p->def = def;
  p->typ = NULL;
  /* typing info is computed after syntax analysis, @see noll_pred_type */

  return p;
}

uid_t
noll_pred_array_find (const char *name)
{
  if (preds_array && (noll_vector_size (preds_array) > 0))
    {
      uint_t sz = noll_vector_size (preds_array);
      for (uint_t i = 0; i < sz; i++)
	if (noll_pred_getpred (i) && !strcmp (name,
					      noll_pred_getpred (i)->pname))
	  return i;
    }
  return UNDEFINED_ID;
}

uid_t
noll_pred_register (const char *pname, noll_pred_binding_t * def)
{
  assert (pname && def);
  uid_t pid = noll_vector_size (preds_array);
  noll_pred_t *p = noll_pred_new (pname, pid, def);
  noll_pred_array_push (preds_array, p);
  return pid;
}

uid_t
noll_pred_typecheck_call (uid_t pid, uid_t * actuals_ty, uid_t size)
{
  if (pid == UNDEFINED_ID)
    return UNDEFINED_ID;
  const noll_pred_t *p = noll_pred_getpred (pid);
  assert (NULL != p);
  if (size != p->def->fargs)
    {
      // TODO: make error message
      printf
	("Predicate call `%s': called with %d parameters instead of %d.\n",
	 p->pname, size, p->def->fargs);
      return UNDEFINED_ID;
    }
  for (uint_t i = 0; i < size; i++)
    {
      noll_var_t *fi = noll_vector_at (p->def->vars, i + 1);	/* +1 for nil */
      uid_t fi_ty = NOLL_TYP_VOID;
      if (fi->vid != VNIL_ID)
	fi_ty = (fi->vty && fi->vty->kind == NOLL_TYP_RECORD) ?
	  noll_vector_at (fi->vty->args, 0) : UNDEFINED_ID;
      if ((actuals_ty[i] != NOLL_TYP_VOID) && (actuals_ty[i] != fi_ty))
	{
	  // TODO: make error message
	  printf ("Predicate call `%s': bad type for the %d-th parameter.\n",
		  p->pname, i);
	  return UNDEFINED_ID;
	}
    }
  return pid;
}

const noll_pred_t *
noll_pred_getpred (uid_t pid)
{
  if (pid >= noll_vector_size (preds_array))
    {
      printf
	("noll_pred_getpred: called with identifier %d not in the global environment.\n",
	 pid);
      return NULL;
    }

  return noll_vector_at (preds_array, pid);
}

const char *
noll_pred_name (uid_t pid)
{
  const noll_pred_t *pred = NULL;
  if ((pred = noll_pred_getpred (pid)) == NULL)
    {
      return "unknown";
    }

  return pred->pname;
}


/** 
 * Total ordering of predicates using their call. 
 * Used the reverse ordering of identifiers, due
 * to the parsing.
 * @return true if not (rhs calls lhs)
 */
bool
noll_pred_order_lt (uid_t lhs, uid_t rhs)
{
  return lhs > rhs;
}

/**
 * Search @p fid inside the fields of predicate @p pid with a role of
 * at most kind.
 * 
 * @param pid  procedd identifier in preds_array
 * @param fid  field identifier in fields_array
 * @param kind max kind to be found for @p fid
 * @return     true if fid has a role at least kind
 */
bool
noll_pred_is_field (uid_t pid, uid_t fid, noll_field_e kind)
{
  assert (pid < noll_vector_size (preds_array));
  assert (fid < noll_vector_size (fields_array));

  noll_pred_t *pred = noll_vector_at (preds_array, pid);
  noll_field_e k = noll_vector_at (pred->typ->pfields, fid);
  return (k <= kind) && ((kind == NOLL_PFLD_NONE) || (k > NOLL_PFLD_NONE));
}

bool
noll_pred_is_null_field (uid_t pid, uid_t fid)
{
  assert (pid < noll_vector_size (preds_array));
  assert (fid < noll_vector_size (fields_array));

  noll_pred_t *pred = noll_vector_at (preds_array, pid);
  noll_field_e k = noll_vector_at (pred->typ->pfields, fid);
  return (k == NOLL_PFLD_NULL);
}

/**
 * Return true if @p fid is a backbone for some predicate.
 * Information computed at typing, @see noll_entl_type.
 */
bool
noll_pred_is_backbone_field (uid_t fid)
{

  assert (fid < noll_vector_size (fields_array));

  noll_field_t *f = noll_vector_at (fields_array, fid);

  assert (f->pid < noll_vector_size (preds_array));

  return noll_pred_is_field (f->pid, fid, NOLL_PFLD_BORDER);
}

bool
noll_pred_is_main_backbone_field (uid_t fid)
{
  assert (fid < noll_vector_size (fields_array));

  noll_field_t *f = noll_vector_at (fields_array, fid);
  assert (NULL != f);
  assert (f->pid < noll_vector_size (preds_array));

  return noll_pred_is_field (f->pid, fid, NOLL_PFLD_BCKBONE);
}

int noll_pred_fill_type (noll_pred_t * p, uint_t level, noll_space_t * form);

/**
 * Type the predicate definitions.
 * @return 0 for incorrect typing
 */
int
noll_pred_type ()
{
  assert (preds_array != NULL);
  assert (fields_array != NULL);
  assert (records_array != NULL);

  int res = 1;
  /* go through all predicates starting with the simpler ones */
  for (uint_t pid = 0;
       pid < noll_vector_size (preds_array) && (res == 1); pid++)
    {
      noll_pred_t *p = noll_vector_at (preds_array, pid);
      /* alloc typing info field */
      p->typ =
	(noll_pred_typing_t *) malloc (sizeof (struct noll_pred_typing_t));

      /* predicate type = type of the first parameter */
      p->typ->ptype0 = noll_var_record (p->def->vars, 1);

      /* types covered */
      p->typ->ptypes = noll_uint_array_new ();
      /* resize the array to cover all the records, filled with 0 */
      noll_uint_array_resize (p->typ->ptypes,
			      noll_vector_size (records_array));
      noll_vector_at (p->typ->ptypes, p->typ->ptype0) = 1;

      /* fields used */
      p->typ->pfields = noll_uint_array_new ();
      /* resize the array to cover all the fields, filled with 0 = NOLL_PFLD_NONE */
      noll_uint_array_resize (p->typ->pfields,
			      noll_vector_size (fields_array));

      /* predicates called */
      p->typ->ppreds = noll_uint_array_new ();
      /* resize the array to cover all the predicates called */
      noll_uint_array_resize (p->typ->ppreds, noll_vector_size (preds_array));

      /* go through the formulas to fill the infos */
      res = noll_pred_fill_type (p, 0, p->def->sigma_0);
      if (res == 0)
	break;
      /* TODO: no need to for level 1 formulas? */
      res = noll_pred_fill_type (p, 1, p->def->sigma_1);
    }
  return res;
}

/**
 * Fill the arguments flds and typs, if not null, with the
 * fields resp. record ids, obtained from formula form.
 * @param p      predicate 
 * @param level  level (0 or 1) of the analyzed formulas 
 * @param form   analyzed formula
 */
int
noll_pred_fill_type (noll_pred_t * p, uint_t level, noll_space_t * form)
{
  if (!form || form->kind == NOLL_SPACE_EMP)
    return 1;
  switch (form->kind)
    {
    case NOLL_SPACE_PTO:
      {
	if (level == 1)
	  return 0;		/* no pto in inner formulas! */
	if (form->m.pto.sid != 1)
	  /* only pto from first argument */
	  return 0;		/* TODO: already checked? */
	for (uid_t i = 0; i < noll_vector_size (form->m.pto.fields); i++)
	  {
	    uid_t fid = noll_vector_at (form->m.pto.fields, i);
	    uid_t dst = noll_vector_at (form->m.pto.dest, i);

	    /* fill type infos with type of dst */
	    uid_t dst_r = noll_var_record (p->def->vars, dst);
	    noll_vector_at (p->typ->ptypes, dst_r) = 1;

	    /* fill field info depending on dst */
	    /* dst is in 0 -- NULL -- to noll_vector_size(p->def->vars) */
	    if (dst == 0)
	      {
		/* dst == NULL */
		noll_vector_at (p->typ->pfields, fid) = NOLL_PFLD_NULL;
	      }
	    else if (dst <= p->def->fargs)
	      {
		/* to the arguments */
		noll_vector_at (p->typ->pfields, fid) = NOLL_PFLD_BORDER;
	      }
	    else if (dst == (p->def->fargs + 1))
	      {
		/* dst == first existential var, then level 0 */
		noll_vector_at (p->typ->pfields, fid) = NOLL_PFLD_BCKBONE;
	      }
	    else
	      {
		/* dst == other existentials */
		for (uint_t ex = p->def->fargs + 2;
		     ex < noll_vector_size (p->def->vars); ex++)
		  if (dst == ex)
		    {
		      noll_vector_at (p->typ->pfields, fid) = NOLL_PFLD_INNER;
		      break;
		    }
	      }
	    if (noll_vector_at (p->typ->pfields, fid) == NOLL_PFLD_NONE)
	      return 0;		/* the field info is not filled correctly */
	  }
	break;
      }
    case NOLL_SPACE_LS:
      {
	uint_t cpid = form->m.ls.pid;
	const noll_pred_t *cp = noll_pred_getpred (cpid);
	/* fill pred info */
	if (cpid != p->pid)
	  noll_vector_at (p->typ->ppreds, cpid) = 1;
	if (cp && cp->typ)
	  {
	    // copy called pred information in the arrays
	    if (cp->typ->pfields)
	      for (uid_t fid = 0; fid < noll_vector_size (fields_array);
		   fid++)
		{
		  noll_field_e cpfkind =
		    noll_vector_at (cp->typ->pfields, fid);
		  noll_field_e pfkind = noll_vector_at (p->typ->pfields, fid);
		  if (cpfkind != NOLL_PFLD_NONE && cpfkind != NOLL_PFLD_NULL)
		    {
		      /* the field is used in cpid and 
		       * it shall not be reused as backbone (level 0) in caller pids */
		      if (pfkind == NOLL_PFLD_BCKBONE)
			{
			  /* error, shared field between predicates : stop ! */
			  fprintf (stderr,
				   "Error in predicate typing: shared backbone field fid-%d!\n",
				   fid);
			  fprintf (stderr,
				   "\t\t between predicates pid-%d < pid-%d\n",
				   p->pid, cpid);
			  // TODO: put in form
			  return 0;
			}
		      noll_vector_at (p->typ->pfields, fid) =
			NOLL_PFLD_NESTED;
		    }
		}
	    if (cp->typ->ptypes)
	      for (uid_t rid = 0; rid < noll_vector_size (records_array);
		   rid++)
		{
		  if (noll_vector_at (cp->typ->ptypes, rid) == 1)
		    noll_vector_at (p->typ->ptypes, rid) = 1;
		}
	  }
	break;
      }
    default:
      {
	// separation formula
	for (uid_t i = 0; i < noll_vector_size (form->m.sep); i++)
	  if (0 ==
	      noll_pred_fill_type (p, level, noll_vector_at (form->m.sep, i)))
	    return 0;
	break;
      }
    }
  return 1;
}

/**
 * Order the fields using the predicate definitions.
 * @return 0 for incorrect ordering
 */
int
noll_field_order ()
{
  uint_t no = 0;
  /* go through the predicates -- in reverse order --
   * and fill the infos on fields */
  for (uint_t pid = noll_vector_size (preds_array) - 1; (pid + 1) >= 1; pid--)
    {
      noll_pred_t *p = noll_vector_at (preds_array, pid);
      /* search the backbones and order them */
      for (uint_t fid = 0; fid < noll_vector_size (fields_array); fid++)
	if (noll_vector_at (p->typ->pfields, fid) == NOLL_PFLD_BCKBONE)
	  {
	    noll_field_t *f = noll_vector_at (fields_array, fid);
	    f->order = no++;	/* TODO test that it is not already filled ! */
	    f->pid = pid;
#ifndef NDEBUG
	    fprintf (stdout, "Field %s @(pid = %d, kind = %d) order=%d\n",
		     f->name, pid,
		     noll_vector_at (p->typ->pfields, fid), f->order);
#endif
	  }
      /* search for inner fields */
      for (uint_t fid = 0; fid < noll_vector_size (fields_array); fid++)
	if (noll_vector_at (p->typ->pfields, fid) == NOLL_PFLD_INNER)
	  {
	    noll_field_t *f = noll_vector_at (fields_array, fid);
	    f->order = no++;	/* TODO test that it is not already filled ! */
	    f->pid = pid;
#ifndef NDEBUG
	    fprintf (stdout, "Field %s @(pid = %d, kind = %d) order=%d\n",
		     f->name, pid,
		     noll_vector_at (p->typ->pfields, fid), f->order);
#endif
	  }
      /* search for NULL fields */
      for (uint_t fid = 0; fid < noll_vector_size (fields_array); fid++)
	if (noll_vector_at (p->typ->pfields, fid) == NOLL_PFLD_NULL)
	  {
	    noll_field_t *f = noll_vector_at (fields_array, fid);
	    if (f->pid == UNDEFINED_ID)
	      {
		/* it is not already filled ! */
		f->order = no++;
		f->pid = pid;
	      }
#ifndef NDEBUG
	    fprintf (stdout, "Field %s @(pid = %d, kind = %d) order=%d\n",
		     f->name, pid,
		     noll_vector_at (p->typ->pfields, fid), f->order);
#endif
	  }
      /* search for to border fields */
      for (uint_t fid = 0; fid < noll_vector_size (fields_array); fid++)
	if (noll_vector_at (p->typ->pfields, fid) == NOLL_PFLD_BORDER)
	  {
	    noll_field_t *f = noll_vector_at (fields_array, fid);
	    f->order = no++;	/* TODO test that it is not already filled ! */
	    f->pid = pid;
#ifndef NDEBUG
	    fprintf (stdout, "Field %s @(pid = %d, kind = %d) order=%d\n",
		     f->name, pid,
		     noll_vector_at (p->typ->pfields, fid), f->order);
#endif
	  }
    }
#ifndef NDEBUG
#endif
  return 1;
}


uid_t
noll_pred_get_minfield (uid_t pid)
{
  const noll_pred_t *pred = noll_pred_getpred (pid);
  assert (NULL != pred);
  assert (NULL != pred->typ);
  const noll_uint_array *fields = pred->typ->pfields;
  assert (NULL != fields);

  uid_t minfield_candidate = (uid_t) - 1;
  for (size_t i = 0; i < noll_vector_size (fields); ++i)
    {
      if (1 == noll_vector_at (fields, i))
	{			// if the field is used in the predicate
	  if (((uid_t) - 1 == minfield_candidate)
	      || noll_field_lt (i, minfield_candidate))
	    {
	      minfield_candidate = i;
	    }
	}
    }

  // make sure that there was some minimum field
  assert ((uid_t) - 1 != minfield_candidate);

  return minfield_candidate;
}



/* ====================================================================== */
/* Printing */
/* ====================================================================== */

void
noll_pred_array_fprint (FILE * f, noll_pred_array * a, const char *msg)
{
  fprintf (f, "\n%s: ", msg);
  fflush (f);
  if (!a)
    {
      fprintf (f, "null\n");
      return;
    }
  fprintf (f, "[");
  uint_t length_a = noll_vector_size (a);
  for (uint_t i = 0; i < length_a; i++)
    {
      noll_pred_t *pi = noll_vector_at (a, i);
      fprintf (f, "pred-%d: %s(%zu args) ", pi->pid, pi->pname,
	       pi->def->pargs);
      fprintf (f, "of type ");
      if (pi->typ != NULL)
	{
	  fprintf (f, " %s, ", noll_record_name (pi->typ->ptype0));
	  fprintf (f, "\n\t\tall types [");
	  if (pi->typ->ptypes != NULL)
	    for (uint_t ti = 0; ti < noll_vector_size (pi->typ->ptypes); ti++)
	      fprintf (f, "%s, ",
		       noll_record_name (noll_vector_at
					 (pi->typ->ptypes, ti)));
	  fprintf (f, "], ");
	  fprintf (f, "\n\t\trec fields [");
	  if (pi->typ->pfields != NULL)
	    for (uint_t fi = 0; fi < noll_vector_size (pi->typ->pfields);
		 fi++)
	      fprintf (f, "%s(%d), ", noll_field_name (fi),
		       noll_vector_at (pi->typ->pfields, fi));
	  fprintf (f, "]\n");
	}
      else
	fprintf (f, "NULL\n");
    }
  fprintf (f, " - ]");
  fflush (f);
}
