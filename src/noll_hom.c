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

#include "noll_types.h"
#include "noll_hom.h"
#include "noll_entl.h"
#include "noll.h"
#include "noll_graph2ta.h"
#include "noll_pred2ta.h"

NOLL_VECTOR_DEFINE (noll_shom_array, noll_shom_t *);

/* ====================================================================== */
/* Constructors/destructors */
/* ====================================================================== */

/* Allocate a homomorphism for the crt problem. */
noll_hom_t *
noll_hom_alloc (void)
{

  assert (noll_prob != NULL);

  noll_hom_t *h = (noll_hom_t *) malloc (sizeof (noll_hom_t));
  h->is_empty = true;
  h->shom = noll_shom_array_new ();
  size_t sz = noll_vector_size (noll_prob->ngraph);
  assert (sz >= 1);
  noll_shom_array_resize (h->shom, noll_vector_size (noll_prob->ngraph));

  return h;
}


/* ====================================================================== */
/* Getters/Setters */
/* ====================================================================== */

/* ====================================================================== */
/* Printers */
/* ====================================================================== */

void
noll_hom_fprint (FILE * f, noll_hom_t * h)
{
  assert (f != NULL);
  if (NULL == h)
    {
      fprintf (f, "NULL\n");
      return;
    }

  if (h->is_empty)
    {
      fprintf (f, "EMPTY\n");
    }

  assert (NULL != h->shom);

  bool isempty = true;
  for (uint_t i = 0; i < noll_vector_size (h->shom); i++)
    {
      noll_shom_t *shi = noll_vector_at (h->shom, i);
      noll_graph_t *ngi = noll_vector_at (noll_prob->ngraph, i);

      if (shi->node_hom == NULL) {
#ifndef NDEBUG
	fprintf (f, "NULL\n");
#endif
	continue;
      }

      /* print node mapping */
      if (isempty) {
	fprintf (f, "[\n");
	isempty = false;
      }
      fprintf (f, "Simple Hom %d for n-graph %zu: \n", i, shi->ngraph);
      fprintf (f, "\tNode mapping (n -> p): ");
      fprintf (f, "[");
      for (uint_t j = 0; j < ngi->nodes_size; j++)
	fprintf (f, "n%d --> n%d,", j, shi->node_hom[j]);
	fprintf (f, "]");

      /* print edge mapping */
      fprintf (f, "\n\tEdge mapping (p -> n): ");
      if (shi->pused == NULL)
	fprintf (f, "NULL\n");
      else
	{
	  fprintf (f, "[");
	  for (uint_t j = 0; j < noll_vector_size (shi->pused); j++)
	    fprintf (f, "e%d --> e%d,", j, noll_vector_at (shi->pused, j));
	  fprintf (f, "]");
	}
    fprintf (f, "\n");
    }
  if (isempty == false)
    fprintf (f, "]\n");
  else
    fprintf (f, "EMPTY\n");

}

/* ====================================================================== */
/* Solver */
/* ====================================================================== */


/**
 * Return the image of args by the mapping h of size size.
 * Add 'nil' at the end if the predicate used 'nil'.
 */
noll_uid_array *
noll_hom_apply_size_array (uint_t * h, uint_t hsize,
     noll_uid_array * args, bool useNil)
{
  noll_uid_array *res = noll_uid_array_new ();
  uint_t sz = noll_vector_size (args);
  noll_uid_array_reserve (res, sz);
  for (uint_t i = 0; i < noll_vector_size (args); i++)
    {
      uint_t n1 = noll_vector_at (args, i);
      if (n1 >= hsize)
	{
	  noll_uid_array_delete (res);
	  res = NULL;
	  return res;
	}
      uint_t n2 = h[n1];
      noll_uid_array_push (res, n2);
    }
  if (useNil) {
    /* add nil at the end of args */
    assert (h[0] == 0); // TODO: check that nil node is always 0
    noll_uid_array_push(res, h[0]);
  }
  return res;
}


/**
 * Given the graph g and the node of type node_ty which is included in term t,
 * fill (toFill=true) or intersect with (toFill=false) ptos (for points to)
 * and pred (for predicate) edges and add the edge id of beta to impl if
 * something is filled/accepted.
 */
void
noll_graph_complete_edge (noll_graph_t * g, noll_uid_array * svar2edge,
			  uint_t node, uint_t node_ty, noll_sterm_t * t,
			  noll_edge_array * ptos, noll_edge_array * preds,
			  noll_uid_array * impl, bool toFill)
{

  if ((&g != &g) || (&node != &node) || (&node_ty != &node_ty) ||
      (&ptos != &ptos) || (&preds != &preds) || (&impl != &impl) ||
      (&toFill != &toFill) || (svar2edge == 0))
    {
      assert (0);		// to avoid the "unused parameter" bug
    }

  assert (svar2edge != NULL);
  assert (t != NULL);
  // get svar attached to beta
  uint_t beta_svar = t->svar;
  // TODO
}

/**
 * Compute the implicit edges in g using the sharing constraints.
 * Change the sharing constraints to keep track of new edges.
 * Adds set location variables to index the new edges.
 */
void
noll_graph_complete (noll_graph_t * g)
{
  if (g->isComplete == true)
    return;
  if ((g->share == NULL) || (noll_vector_size (g->share) == 0))
    {
      g->isComplete = true;
      return;
    }

  // Step1: build the mapping svar2edge: slocs -> edge
  noll_uid_array *svar2edge = noll_uid_array_new ();
  noll_uid_array_reserve (svar2edge, noll_vector_size (g->svars));
  for (uint_t i = 0; i < noll_vector_size (g->svars); i++)
    noll_uid_array_push (svar2edge, UNDEFINED_ID);
  for (uint_t i = 0; i < noll_vector_size (g->edges); i++)
    {
      noll_edge_t *ei = noll_vector_at (g->edges, i);
      if ((ei->kind == NOLL_EDGE_PRED) && (ei->bound_svar != UNDEFINED_ID))
	noll_vector_at (svar2edge, ei->bound_svar) = i;
    }

  // Step2: go through the sharing constraints
  // TODO: it works only if the set of sharing constraints is minimum
  for (uint_t i = 0; i < noll_vector_size (g->share); i++)
    {
      noll_atom_share_t *s = noll_vector_at (g->share, i);
      if ((s->kind == NOLL_SHARE_NI) || (s->kind > NOLL_SHARE_SUBSET))
	continue;
      // declare the node and the type that will be constrained by the constraint
      uint_t node = UNDEFINED_ID;
      uint_t node_ty = UNDEFINED_ID;
      if (s->kind == NOLL_SHARE_IN)
	{
	  assert (s->t_left != NULL);
	  assert (s->t_left->lvar < noll_vector_size (g->lvars));
	  // constrain node in U beta_i
	  node = g->var2node[s->t_left->lvar];
	  node_ty = noll_var_record (g->lvars, s->t_left->lvar);
	}
      else
	{
	  assert (s->kind == NOLL_SHARE_SUBSET);
	  assert (s->t_left->svar < noll_vector_size (g->svars));
	  // constraint alpha <= U beta_i
	  // get the index of alpha and the projection type, if any
	  uint_t alpha = s->t_left->svar;
	  uint_t alpha_ty = (s->t_left->lvar == UNDEFINED_ID) ? UNDEFINED_ID
	    : noll_var_record (g->lvars, s->t_left->lvar);
	  // get the edge bound to alpha
	  uint_t alpha_ei = noll_vector_at (svar2edge, alpha);
	  if (alpha_ei == UNDEFINED_ID)	// no edge bound
	    continue;
	  noll_edge_t *alpha_e = noll_vector_at (g->edges, alpha_ei);
	  uint_t alpha_pid = alpha_e->label;
	  if (alpha_e->impl != NULL && noll_vector_size (alpha_e->impl) >= 1)
	    // implicit edge, nothing to do
	    continue;
	  // get the source of this edge
	  node = noll_vector_at (alpha_e->args, 0);
	  // get the type of the node start of alpha = type of the predicate
	  const noll_pred_t *pred = noll_pred_getpred (alpha_pid);
	  assert (NULL != pred);
	  node_ty = pred->typ->ptype0;
	  if ((alpha_ty != UNDEFINED_ID) && (alpha_ty != node_ty))
	    // alpha is projected on a inner type, thus not a program variable
	    // for this type in the edge bound to alpha
	    // TODO: we suppose that constraints are fully saturated
	    continue;
	}
      // The  node of type node_ty is included in some of the sterms in s->t_right.
      // Get the common properties of all the terms in sterm, start with first.
      assert (s->t_right != NULL);
      assert (noll_vector_size (s->t_right) > 0);
      noll_edge_array *ptos = noll_edge_array_new ();
      noll_edge_array *preds = noll_edge_array_new ();
      noll_uid_array *impl = noll_uid_array_new ();
      // TODO: fills ptos ands preds with constraints
      noll_graph_complete_edge (g, svar2edge, node, node_ty, noll_vector_at (s->t_right, 0), ptos, preds, impl, true);	// fill
      // intersect ptos and preds with the others members of the unions
      // if they include type node_ty
      for (uint_t i = 1; i < noll_vector_size (s->t_right); i++)
	{
	  noll_graph_complete_edge (g, svar2edge, node, node_ty, noll_vector_at (s->t_right, i), ptos, preds, impl, false);	// intersect
	}
      // TODO
      //      if ptos != emptyset then
      //         add edge pto and say that it is implicit from U beta_i
      //      if preds != emptyset then
      //         add edge pred and say that it is implicit from U beta_i
      //         add a new svar and bound it to pred
      //         add constraint svar <= U beta_i
      if (noll_vector_size (s->t_right) == 1)
	{
	  //    if tysrc = type of beta_0 then
	  //      split edge beta_0 in two edges to nsrc and from nsrc
	  //      add two new svar variables s1, s2 bound to the two edges
	  //      add constraints beta_0 <= s_1 U s_2 and s1 <= beta_0 and s_2 <= beta_0
	}

    }

  g->isComplete = true;
}

/**
 * Try to match formula form with vars used mapped to nodes by mapvar,
 * and push the edges mapped to res.
 */
int
noll_graph_get_edge_form (noll_graph_t * g, noll_space_t * form,
			  noll_uid_array * mapvar, noll_uid_array * res)
{

  assert (g != NULL);
  assert (form != NULL);
  assert (mapvar != NULL);
  assert (res != NULL);

  switch (form->kind)
    {
    case NOLL_SPACE_EMP:
      // nothing to do
      return 1;
    case NOLL_SPACE_PTO:
      {
	// node on which is mapped the source var
	assert (form->m.pto.sid < noll_vector_size (mapvar));
	uint_t nsrc = noll_vector_at (mapvar, form->m.pto.sid);
#ifndef NDEBUG
	printf ("%s\n", noll_vector_at (g->lvars, nsrc)->vname);
	printf ("%s\n", noll_vector_at (g->lvars, form->m.pto.sid)->vname);
#endif
	// search in g the same fields from nsrc
	if (g->mat[nsrc] != NULL)
	  {
	    noll_uid_array *tmp_res = noll_uid_array_new ();	// temporary array of edges
	    for (uint_t i = 0; i < noll_vector_size (form->m.pto.fields); i++)
	      {
		uint_t fid = noll_vector_at (form->m.pto.fields, i);
		// search the pto edge in g
		bool found = false;
		for (uint_t j = 0;
		     j < noll_vector_size (g->mat[nsrc]) && !found; j++)
		  {
		    uint_t ej = noll_vector_at (g->mat[nsrc], j);
		    noll_edge_t *edge_j = noll_vector_at (g->edges, ej);
		    if ((edge_j->kind == NOLL_EDGE_PTO) && (edge_j->label
							    == fid))
		      {
			// ok, it matched
			found = true;
			// push the field first
			noll_uid_array_push (tmp_res, ej);
			// verify/update mapping of variables
			uint_t vdst = noll_vector_at (form->m.pto.dest, i);
			if (noll_vector_at (mapvar, vdst) == UNDEFINED_ID)
			  noll_vector_at (mapvar, vdst)
			    = noll_vector_at (edge_j->args, 1);
			assert (noll_vector_at (mapvar, vdst) ==
				noll_vector_at (edge_j->args, 1));
		      }
		  }
		if (!found)
		  {
		    // no match for this edge
		    fprintf (stdout,
			     "Edge mapping fails: g2 edge from node %d for field %d!\n",
			     nsrc, fid);
		    fflush (stdout);
		    noll_uid_array_delete (tmp_res);
		    // TODO: shall also remove mapping from mapvar!
		    return 0;
		  }
	      }
	    // move edges to result
	    for (uint_t i = 0; i < noll_vector_size (tmp_res); i++)
	      noll_uid_array_push (res, noll_vector_at (tmp_res, i));
	    noll_uid_array_delete (tmp_res);
	  }
	else
	  {
	    fprintf (stdout,
		     "Edge mapping fails: g2 points-to edge from node %d!\n",
		     nsrc);
	    fflush (stdout);
	    return 0;
	  }
	break;
      }
    case NOLL_SPACE_LS:
      {
	// Search edge labeled by form->label and some arguments mapped like mapvar
	uint_t pid = form->m.ls.pid;
	// build the array of node arguments
	uint_t farg = UNDEFINED_ID;	// first arg mapped to a node
	noll_uid_array *nargs = noll_uid_array_new ();
	for (uint_t i = 0; i < noll_vector_size (form->m.ls.args); i++)
	  {
	    uint_t vi = noll_vector_at (form->m.ls.args, i);
	    uint_t ni = noll_vector_at (mapvar, vi);
	    noll_uid_array_push (nargs, ni);
	    if (ni != UNDEFINED_ID && farg == UNDEFINED_ID)
	      farg = ni;
	  }
	if (farg == UNDEFINED_ID)
	  {
	    // very big choice of mappings in g, signal it
#ifndef NDEBUG
	    fprintf (stdout,
		     "Edge mapping: too much choices for edge with predicate %d!",
		     pid);
	    fflush (stdout);
#endif
	  }
	// search edge in g with same arguments
	uint_t found_ei = UNDEFINED_ID;
	for (uint_t ei = 0; (ei < noll_vector_size (g->edges)) && (found_ei
								   ==
								   UNDEFINED_ID);
	     ei++)
	  {
	    noll_edge_t *edge_i = noll_vector_at (g->edges, ei);
	    if (edge_i->kind == NOLL_EDGE_PRED && edge_i->label == pid)
	      {
		// same predicate, verify args
		bool same = true;
		for (uint_t i = 0;
		     i < noll_vector_size (edge_i->args) && same; i++)
		  if ((noll_vector_at (nargs, i) != UNDEFINED_ID)
		      && (noll_vector_at (nargs, i) !=
			  noll_vector_at (edge_i->args, i)))
		    same = false;
		if (same)
		  {
		    // push ei in result
		    found_ei = ei;
#ifndef NDEBUG
		    fprintf (stdout,
			     "Edge mapping: g2 edge %d mapped to formula!\n",
			     ei);
		    fflush (stdout);
#endif
		    noll_uid_array_push (res, ei);
		    // update mapvar
		    for (uint_t i = 0; i < noll_vector_size (edge_i->args)
			 && same; i++)
		      if (noll_vector_at (nargs, i) == UNDEFINED_ID)
			{
			  uint_t vi = noll_vector_at (form->m.ls.args, i);
			  noll_vector_at (mapvar, vi)
			    = noll_vector_at (edge_i->args, i);
			}
		  }
	      }
	  }
	noll_uid_array_delete (nargs);
	if (found_ei == UNDEFINED_ID)
	  {
	    fprintf (stdout,
		     "Edge mapping fails: g2 edge with predicate %d!\n", pid);
	    fflush (stdout);
	    return 0;
	  }
	break;
      }
    case NOLL_SPACE_SSEP:
      {
	// TODO: break as soon as not matching
	noll_uid_array **tres =
	  (noll_uid_array **) malloc (noll_vector_size (form->m.sep) *
				      sizeof (noll_uid_array *));
	uint_t i = 0;
	for (; i < noll_vector_size (form->m.sep); i++)
	  {
	    tres[i] = noll_uid_array_new ();
	    int r =
	      noll_graph_get_edge_form (g, noll_vector_at (form->m.sep, i),
					mapvar, tres[i]);
	    if (r == 0)
	      break;
	  }
	if (i == noll_vector_size (form->m.sep))
	  {
	    // success,
	    // TODO: verify separation
	    // push edges to res
	    for (; i < noll_vector_size (form->m.sep); i++)
	      {
		for (uint_t j = 0; j < noll_vector_size (tres[i]); j++)
		  {
		    noll_uid_array_push (res, noll_vector_at (tres[i], j));
		  }
		noll_uid_array_delete (tres[i]);
	      }
	    free (tres);
	  }
	else
	  return 0;
	break;
      }
    case NOLL_SPACE_WSEP:
#ifndef NDEBUG
      fprintf (stdout, "NYI: wsep formula for predicate definition!\n");
      fflush (stdout);
#endif
      return 0;
    default:
      break;
    }

  return 1;
}

/**
 * Fill res with the edges of g covering the edge of kind and label and args.
 */
void
noll_graph_get_edge_path (noll_graph_t * g, noll_edge_e kind, uint_t label,
			  noll_uid_array * args, noll_uid_array * res)
{

  // store of edge identifiers matching the searched edge in this function
  noll_uid_array *temp_res = noll_uid_array_new ();
  uint_t uint_temp = noll_vector_size (temp_res);
  // array used to store the new arguments when searching a path
  // from a new source node
  noll_uid_array *args0 = noll_uid_array_new ();
  // source and destination nodes for edge searched
  uint_t nsrc = noll_vector_at (args, 0);
  uint_t ndst = noll_vector_at (args, 1);
  // a new intermediary node
  uint_t nend = UNDEFINED_ID;

#ifndef NDEBUG
  fprintf (stdout,
	   "---- Search path for edge n%d---(kind=%d, label=%d)-->n%d:\n",
	   nsrc, kind, label, ndst);
#endif

  if (g->mat[nsrc] != NULL)
    {
      for (uint_t i = 0; i < noll_vector_size (g->mat[nsrc]); i++)
	{
	  uint_t ei = noll_vector_at (g->mat[nsrc], i);
	  noll_edge_t *edge_i = noll_vector_at (g->edges, ei);
	  if ((edge_i->kind == kind) && (edge_i->label == label)
	      && (noll_vector_size (edge_i->args) == noll_vector_size (args)))
	    {
#ifndef NDEBUG
	      fprintf (stdout, "\t found e%d, same kind and label\n", ei);
#endif
	      // edge found with the same kind, label and args size,
	      // check the other arguments than source and destination nodes are equal
	      bool ishom = true;
	      for (uint_t j = 2; j < noll_vector_size (args)
		   && (ishom == true); j++)
		if (noll_vector_at (args, j)
		    != noll_vector_at (edge_i->args, j))
		  {
#ifndef NDEBUG
		    fprintf (stdout,
			     "\t\t but different arg %d (n%d != n%d)\n", j,
			     noll_vector_at (args, j),
			     noll_vector_at (edge_i->args, j));
#endif
		    ishom = false;
		  }
	      if (ishom == true)
		{
#ifndef NDEBUG
		  fprintf (stdout, "\t\t and same args\n");
#endif
		  noll_uid_array_push (temp_res, ei);
		  nend = noll_vector_at (edge_i->args, 1);	// destination of the edge
		}
	    }
	}
    }

  uint_temp = noll_vector_size (temp_res);
#ifndef NDEBUG
  fprintf (stdout, "\t %d edges matches!\n", uint_temp);
#endif

  // The positive case: edge match and destination nodes match
  // both kind of edges
  if ((uint_temp > 0) && (nend == ndst))
    {
      // an edge has been found and the destination node is the same
      // move from temp_res to res
      goto path_ok;
    }

  // The negative case: for PTO edge, either no edge found
  // OR pto edge found but not the good destination node
  if ((kind == NOLL_EDGE_PTO) && ((uint_temp == 0)
				  || ((noll_vector_size (temp_res) > 0)
				      && (nend != ndst))))
    {
      // nothing to be done
      goto path_nok;
    }

  assert (kind == NOLL_EDGE_PRED);
  // The negative case: for PRED edge, no edge found
  if (uint_temp == 0)
    {
      // try to match predicate definition
      const noll_pred_t *p = noll_pred_getpred (label);
      assert (NULL != p);
      // init mapping of variables to nodes for this definition, UNDEFINED_ID if not known
      noll_uid_array *mapvar = noll_uid_array_new ();
      for (uint_t i = 0; i < noll_vector_size (p->def->vars); i++)
	noll_uid_array_push (mapvar, UNDEFINED_ID);
      // TODO: correct?
      for (uint_t i = 0; i < noll_vector_size (args); i++)
	noll_vector_at (mapvar, i) = noll_vector_at (args, i);
      // match sigma_0 of the predicate
      noll_graph_get_edge_form (g, p->def->sigma_0, mapvar, temp_res);
      // this call will return at least one edge if found one
      uint_temp = noll_vector_size (temp_res);
      if (uint_temp == 0)
	goto path_nok;
      // if succeed try also sigma_1 from nsrc if not null
      if (p->def->sigma_1 != NULL)
	{
	  noll_uid_array *temp_res1 = noll_uid_array_new ();
	  noll_graph_get_edge_form (g, p->def->sigma_1, mapvar, temp_res1);
	  if (noll_vector_size (temp_res1) == 0)
	    {
	      // error
	      noll_uid_array_delete (temp_res1);
	      goto path_nok;
	    }
	  // else, push the result in temp_res
	  uint_temp = noll_vector_size (temp_res);
	}
      // the predicate succeed on nsrc,
      // see if there is another intermediate node, look at first edge recorded
      uint_t forward_e = noll_vector_at (temp_res, 0);
      nend = noll_vector_at (noll_vector_at (g->edges, forward_e)->args, 1);
      if (nend == ndst)
	{
	  // no intermediate node, push the result in res
	  goto path_ok;
	}
      // there is an intermediate node,
      // continue with the positive case above
    }

  // The positive case: there is a predicate edge or match
  // try this function again with nend as initial node
  // TODO: transform it in a loop
  noll_uid_array_copy (args0, args);
  noll_vector_at (args0, 0) = nend;
  noll_graph_get_edge_path (g, kind, label, args0, temp_res);
  // if it worked, then push the edges in res
  if (noll_vector_size (temp_res) > uint_temp)
    {
    path_ok:
#ifndef NDEBUG
      fprintf (stdout, "=== path found-size%d: [", uint_temp);
#endif
      for (uint_t i = 0; i < noll_vector_size (temp_res); i++)
	{
	  noll_uid_array_push (res, noll_vector_at (temp_res, i));
#ifndef NDEBUG
	  fprintf (stdout, "%d,", i);
#endif
	}
#ifndef NDEBUG
      fprintf (stdout, "]\n");
#endif
    }

path_nok:noll_uid_array_delete (args0);
  noll_uid_array_delete (temp_res);
  return;
}



/**
 * Return the edges of g which can represent an edge
 * of kind between nodes in args and label l.
 */
noll_uid_array *
noll_graph_get_edge (noll_graph_t * g, noll_edge_e kind,
		     noll_uid_array * args, uint_t label)
{
  assert (g != NULL);
  assert (args != NULL);
  assert (noll_vector_size (args) >= 2);
  assert (kind == NOLL_EDGE_PTO || kind == NOLL_EDGE_PRED);

  noll_uid_array *res = noll_uid_array_new ();

  // First try: search a path from nsrc with this label
  noll_graph_get_edge_path (g, kind, label, args, res);
  if (noll_vector_size (res) > 0)
    return res;

  // If not such edge is found, two choices:
  // A) need to saturate, and thus change constraints in g (for pto and ls edges)
  // B) there is a path, not a single edge (for ls edges)
  // The order of dealing A followed by B, but some times only B is needed
  if ((noll_vector_size (res) == 0) && (g->isComplete == false))
    {
      noll_graph_complete (g);	// A: saturation only fill implicit constraints
      // This can be done incrementally, only to cover this edge or fully
    }

  // B: second try, search the path
  noll_graph_get_edge_path (g, kind, label, args, res);

  // if saturation gives nothing, return NULL
  if (noll_vector_size (res) == 0)
    {
      noll_uid_array_delete (res);
      res = NULL;
    }

  return res;
}

/**
 * Return 1 if the edge e has been already mapped by used,
 * otherwise 0.
 */
int
noll_graph_used (noll_uid_array * used, uint_t e, noll_graph_t * g)
{
  assert (used != NULL);
  assert (e < noll_vector_size (used));

  if (&g != &g)
    {
      assert (0);
    }

  // directly used
  if (noll_vector_at (used, e) != UNDEFINED_ID)
    return 1;

  // TODO: some implied edge used?

  return 0;
}


/*
 * For any pointer field f, check if there exists a path with f between any two nodes
 * return[f][x][y]= 1 if there exists an f-path from x to y,
 * 					2 if there exists such a path which consists of edges in edge_set
 * 					0, otherwise
 *
 */

int ***
noll_graph_paths_fields (noll_graph_t * g, noll_uid_array * edge_set)
{

  bool *in_set =
    (bool *) malloc (noll_vector_size (g->edges) * sizeof (bool));
  for (uint_t i = 0; i < noll_vector_size (g->edges); i++)
    {
      in_set[i] = false;
    }
  for (uint_t i = 0; i < noll_vector_size (edge_set); i++)
    in_set[noll_vector_at (edge_set, i)] = true;

  int ***paths = (int ***) malloc (noll_vector_size (fields_array)
				   * sizeof (int **));
  for (uint_t i = 0; i < noll_vector_size (fields_array); i++)
    {
      paths[i] = (int **) malloc (g->nodes_size * sizeof (int *));
      for (uint_t j = 0; j < g->nodes_size; j++)
	{
	  paths[i][j] = (int *) malloc (g->nodes_size * sizeof (int));
	  for (uint_t k = 0; k < g->nodes_size; k++)
	    paths[i][j][k] = 0;
	}
    }
  for (uint_t ei = 0; ei < noll_vector_size (g->edges); ei++)
    {
      noll_edge_t *e = noll_vector_at (g->edges, ei);
      uint_t label = e->label;
      uint_t src = noll_vector_at (e->args, 0);
      uint_t dst = noll_vector_at (e->args, 1);

      if (e->kind == NOLL_EDGE_PTO)
	{
	  paths[label][src][dst] = in_set[ei] ? 2 : 1;

	  for (uint_t ni = 0; ni < g->nodes_size; ni++)
	    if (paths[label][ni][src])
	      {
		paths[label][ni][dst] = ((paths[label][ni][src] == 2)
					 && in_set[ei]) ? 2 : 1;
	      }
	}
      else if (e->kind == NOLL_EDGE_PRED)
	{
	  const noll_pred_t *pred = noll_pred_getpred (label);
	  assert (NULL != pred);
	  /* put each field of level0 on the path */
	  /* MS: change of infos on fields */
	  for (uint_t f = 0; f < noll_vector_size (fields_array); f++)
	    if (noll_pred_is_field (label, f, NOLL_PFLD_BORDER))
	      {
		paths[f][src][dst] = in_set[ei] ? 2 : 1;
		for (uint_t ni = 0; ni < g->nodes_size; ni++)
		  if (paths[label][ni][src])
		    {
		      paths[label][ni][dst] = ((paths[label][ni][src] == 2)
					       && in_set[ei]) ? 2 : 1;
		    }

	      }
	}
      else
	{
#ifndef NDEBUG
	  printf ("Edge type not considered\n");
#endif
	}

    }

  bool cont = true;
  while (cont)
    {
      cont = false;
      for (uint_t i = 0; i < noll_vector_size (fields_array); i++)
	for (uint_t j = 0; j < g->nodes_size; j++)
	  for (uint_t k = 0; k < g->nodes_size; k++)
	    for (uint_t t = 0; t < g->nodes_size; t++)
	      if (paths[i][j][k] && paths[i][k][t])
		{
		  int temp = (paths[i][j][k] == 2 && paths[i][k][t]
			      == 2) ? 2 : 1;
		  if (temp != paths[i][j][t])
		    cont = true;
		  paths[i][j][t] = temp;
		}

    }

#ifndef NDEBUG
  for (uint_t i = 0; i < noll_vector_size (fields_array); i++)
    {
      for (uint_t j = 0; j < g->nodes_size; j++)
	{
	  for (uint_t k = 0; k < g->nodes_size; k++)
	    if (paths[i][j][k])
	      printf ("Between n%d and n%d there is an %s-path=%d\n", j, k,
		      noll_vector_at (fields_array, i)->name, paths[i][j][k]);
	}
    }
#endif

  return paths;
}

/*
 * For each node n of the graph g and each pointer field f,
 * it tests if f is surely defined in n
 * the second argument is the matrix that contains the existing f-paths for any f
 */

bool **
noll_graph_field_defined (noll_graph_t * g, int ***paths)
{
  bool **res = (bool **) malloc (g->nodes_size * sizeof (bool *));
  for (uint_t i = 0; i < g->nodes_size; i++)
    {
      res[i] =
	(bool *) malloc (noll_vector_size (fields_array) * sizeof (bool));
      for (uint_t j = 0; j < noll_vector_size (fields_array); j++)
	res[i][j] = false;
    }

  // for any points-to edge labeled by f and starting in src, f is defined in src and any node from
  // which there exists an f-path to src
  for (uint_t i = 0; i < noll_vector_size (g->edges); i++)
    {
      noll_edge_t *e = noll_vector_at (g->edges, i);
      if (e->kind == NOLL_EDGE_PTO)
	{
	  uint_t f = e->label;
	  uint_t src = noll_vector_at (e->args, 0);
	  res[src][f] = true;
#ifndef NDEBUG
	  printf ("Field %s defined in n%d\n",
		  noll_vector_at (fields_array, f)->name, src);
#endif
	  for (uint_t i = 0; i < g->nodes_size; i++)
	    if (paths[f][i][src])
	      {
		res[i][f] = true;
#ifndef NDEBUG
		printf ("Field %s defined in n%d\n",
			noll_vector_at (fields_array, f)->name, i);
#endif
	      }
	}
    }

  // for any disequality edge (i,j),
  //                      if there exists an f-path between i and j then f is defined in i
  //                      if there exists a node k s.t. there exists an f-path between k and i and an f-path between k and j
  //                                      then f is defined in k
  for (uint_t i = 0; i < g->nodes_size; i++)
    for (int j = i - 1; j >= 0; j--)
      {
	bool diff = g->diff[i][j];
	for (uint_t f = 0; f < noll_vector_size (fields_array); f++)
	  {
	    if (diff & paths[f][i][j])
	      {
		res[i][f] = true;
#ifndef NDEBUG
		printf ("Field %s defined in n%d\n",
			noll_vector_at (fields_array, f)->name, i);
#endif
	      }
	    for (uint_t k = 0; k < g->nodes_size; k++)
	      {
		if (paths[f][k][i] && paths[f][k][j])
		  {
		    res[k][f] = true;
#ifndef NDEBUG
		    printf ("Field %s defined in n%d\n",
			    noll_vector_at (fields_array, f)->name, k);
#endif
		  }
	      }
	  }

      }
  return res;
}

/*
 * Returns 1 if the set of edges edge_set represent a precise unfolding
 * of the edge edge_i1 in g1, i.e., the edges define acyclic paths; the
 * image of the nodes incident to edge_i1 by the homomorphism h is args2
 */
int
noll_graph_check_acyclicity (noll_graph_t * g, noll_uid_array * edge_set)
{
#ifndef NDEBUG
  printf ("===Call to acyclic\n");
#endif
  int ***paths = noll_graph_paths_fields (g, edge_set);
  bool **def_fields = noll_graph_field_defined (g, paths);
  for (uint_t i = 0; i < noll_vector_size (edge_set); i++)
    for (uint_t j = i + 1; j < noll_vector_size (edge_set); j++)
      {
	noll_edge_t *e1 =
	  noll_vector_at (g->edges, noll_vector_at (edge_set, i));
	noll_edge_t *e2 =
	  noll_vector_at (g->edges, noll_vector_at (edge_set, j));
	uint_t dest1 = noll_vector_at (e1->args, 1);
	uint_t dest2 = noll_vector_at (e2->args, 1);
	bool isdiff = (dest1 < dest2) ? g->diff[dest2][dest1]
	  : g->diff[dest1][dest2];
	// if the destinations of the two edges are not equal it is ok
	if (isdiff)
	  continue;

	// otherwise, check if there exists some f-path between the destinations of the
	// two edges such that f is surely defined in the destination of the second edge
	bool disapear = false;
	for (uint_t f = 0; f < noll_vector_size (fields_array); f++)
	  if (paths[f][dest1][dest2] == 2 && def_fields[dest2][f])
	    {
	      disapear = true;
	      break;
	    }
	if (disapear)
	  continue;
#ifndef NDEBUG
	printf ("===Return from acyclic 0\n");
#endif
	return 0;
      }
#ifndef NDEBUG
  printf ("===Return from acyclic 1\n");
#endif
  return 1;
}

int noll_graph_shom (noll_hom_t * h, size_t i);

/**
 * Search a homomorphism to prove noll_prob.
 * Store the homomorphism found in noll_prob->hom.
 * @return 1 if hom found, < 1 otherwise
 */
int
noll_graph_homomorphism (void)
{

  assert (noll_prob != NULL);

  /* allocate the homomorphism */
  noll_hom_t *h = noll_hom_alloc ();

  /* compute a simple homomorphism for each negative graph */
  int res = 0;
  for (size_t i = 0; i < noll_vector_size (noll_prob->ngraph); i++)
    {
      res = noll_graph_shom (h, i);
      /* TODO: update with the algo for disjunctions */
      if (res == 1)
	{
	  break;
	}
    }
  noll_prob->hom = h;
  return res;
}

/**
 * Build node_hom component by mapping
 * all nodes in @p g1 to nodes in @p g2
 * such that the labeling with reference vars is respected
 * and the difference constraints of g1 are in g2.
 *
 * @param g1  domain graph for the homomorphism
 * @param g2  co-domain graph
 * @return    the mapping built, NULL otherwise
 */
uint_t *
noll_graph_shom_nodes (noll_graph_t * g1, noll_graph_t * g2)
{
  assert (g1 != NULL);
  assert (g2 != NULL);

  int res = 1;
  uint_t *n_hom = NULL;
  n_hom = (uint_t *) malloc (g1->nodes_size * sizeof (uint_t));
  /* initialize entries with the default value */
  for (uint_t i = 0; i < g1->nodes_size; i++)
    n_hom[i] = UNDEFINED_ID;
  for (uint_t v = 0; v < noll_vector_size (g1->lvars); v++)
    {
      // TODO: incorrect now with local vars, check the name of the variable
      uint_t n1v = g1->var2node[v];
      uint_t v2 = noll_var_array_find_local (g2->lvars,
					     noll_var_name (g1->lvars, v,
							    NOLL_TYP_RECORD));
      uint_t n2v = g2->var2node[v2];
      if (n1v != UNDEFINED_ID)
	{
	  if (n2v != UNDEFINED_ID)
	    n_hom[n1v] = n2v;
	  else
	    {
	      res = 0;
	      goto return_shom_nodes;
	    }
	}
    }
  /* Check that all nodes of g1 are mapped,
   * assert: all nodes of g1 are labeled by reference vars
   */
  for (uint_t i = 0; i < g1->nodes_size; i++)
    if (n_hom[i] == UNDEFINED_ID)
      {
	res = 0;
	fprintf (stdout, "Node n%d of right side graph not mapped!", i);
	goto return_shom_nodes;
      }

#ifndef NDEBUG
  fprintf (stdout,
	   "Homomorphism built from the labeling with program variables:\n\t[");
  for (uint_t i = 0; i < g1->nodes_size; i++)
    fprintf (stdout, "n%d --> n%d,", i, n_hom[i]);
  fprintf (stdout, "]\n");
#endif

  /*
   * Check that difference edges in g1 are mapped to diff edges in g2
   * assert: all difference edges are in g2, because g2 is normalized
   */
  for (uint_t ni1 = 1; ni1 < g1->nodes_size; ni1++)
    {
      for (uint_t nj1 = 0; nj1 < ni1; nj1++)
	{
	  if (g1->diff[ni1][nj1])
	    {
	      uint_t ni2 = n_hom[ni1];
	      uint_t nj2 = n_hom[nj1];
	      bool isdiff2 = (ni2 < nj2) ? g2->diff[nj2][ni2]
		: g2->diff[ni2][nj2];
	      if (isdiff2 == false)
		{
		  res = 0;
		  // TODO: put message with program variables
		  fprintf (stdout,
			   "The difference edge (n%d != n%d) in the right side graph ",
			   ni1, nj1);
		  fprintf (stdout,
			   "is not mapped to (n%d != n%d) in the left side graph!",
			   ni2, nj2);
		  goto return_shom_nodes;
		}
	    }
	}
    }

return_shom_nodes:
  if (res == 0)
    {
      free (n_hom);
      n_hom = NULL;
    }
  return n_hom;
}

/**
 * Build pto_hom component by mapping
 * all pto edges in @p g1 to pto edges in @p g2
 * such that the labeling with fields is respected.
 * Mark the mapped edges of @p g2 in usedg2.
 *
 * @param g1     domain graph for the homomorphism
 * @param g2     co-domain graph
 * @param n_hom  node mapping
 * @return       the mapping built, NULL otherwise
 */
noll_uid_array *
noll_graph_shom_pto (noll_graph_t * g1, noll_graph_t * g2,
		     uint_t * n_hom, noll_uid_array * usedg2)
{
  assert (g1 != NULL);
  assert (g2 != NULL);
  assert (n_hom != NULL);
  assert (usedg2 != NULL);

  /* initialize the result with undefined identifiers */
  noll_uid_array *pto_hom = noll_uid_array_new ();
  noll_uid_array_reserve (pto_hom, noll_vector_size (g1->edges));

  /* go through the pto edges of g1 and see edges of g2
   * stop when a pto edge is not mapped
   */
  bool isHom = true;
  for (uint_t ei1 = 0;
       (ei1 < noll_vector_size (g1->edges)) && (isHom == true); ei1++)
    {
      /* put an initial value */
      noll_vector_at (pto_hom, ei1) = UNDEFINED_ID;
      noll_edge_t *e1 = noll_vector_at (g1->edges, ei1);
      if (e1->kind != NOLL_EDGE_PTO)
	{
	  continue;
	}
      /* search the pto edge in g2 */
      uid_t nsrc_e1 = noll_vector_at (e1->args, 0);
      uid_t ndst_e1 = noll_vector_at (e1->args, 1);
#ifndef NDEBUG
      fprintf (stdout, "---- Search pto edge n%d ---label=%d)--> n%d:\n",
	       nsrc_e1, e1->label, ndst_e1);
#endif
      isHom = false;
      uint_t nsrc_e2 = n_hom[nsrc_e1];
      uint_t ndst_e2 = n_hom[ndst_e1];
      /* the edge shall start from nsrc_e2 in g2 */
      if (g2->mat[nsrc_e2] != NULL)
	{
	  for (uint_t i = 0;
	       (i < noll_vector_size (g2->mat[nsrc_e2])) && (isHom == false);
	       i++)
	    {
	      uint_t ei2 = noll_vector_at (g2->mat[nsrc_e2], i);
	      noll_edge_t *e2 = noll_vector_at (g2->edges, ei2);
	      if ((e2->kind == NOLL_EDGE_PTO) &&
		  (e2->label == e1->label) &&
		  (noll_vector_at (e2->args, 1) == ndst_e2))
		{
#ifndef NDEBUG
		  fprintf (stdout, "\t found e%d, same label, same kind\n",
			   ei2);
#endif
		  isHom = true;
		  /* mark edge e2 used */
		  noll_vector_at (usedg2, ei2) = ei1;
		  /* fill the hom */
		  noll_vector_at (pto_hom, ei1) = ei2;
		}
	    }
	}
      if (isHom == false)
	{
#ifndef NDEBUG
	  fprintf (stdout, "\t not found!");
#endif
	  /* failure */
	  fprintf (stdout, "\nDiagnosis of failure: ");
	  fprintf (stdout, "points-to edge n%d ---%s--> n%d not mapped!\n",
	       nsrc_e1, noll_field_name(e1->label), ndst_e1);
	}
      /* else, continue */
    }
  /* mapping succeded if isHom = true,
   * otherwise free the allocated structures and return NULL
   */
  if (isHom == false)
    {
      noll_uid_array_delete (pto_hom);
      pto_hom = NULL;
    }
  return pto_hom;
}

/**
 * Select the subgraph of g mapping the predicate
 * with name @p label and arguments @p args.
 * The selected subgraph is put in a copy of @p g, say g2, where
 * only the edges encoding the predicate are presented.
 *
 * First, a set of nodes Vg in g is computed as the set of nodes
 * reachable using the edges of g labeled by
 * L2 = set of fields in @p label and predicate labels usied in @p label
 * on the paths from args[0] to args[1..] or
 * on cyclic paths from args[0].
 * (Nodes used as arguments on predicate edges are also marked.)
 * Then, edges outgoing from Vg \ args[2..] (border) are all marked
 * as used (even not labeled by labels in l2) because they cannot be
 * used by another predicate (from the * semantics).
 * The subgraph g2 is defined as the set of edges labeled with L2
 * and outgoing from Vg \ args[2..], and the set of difference edges
 * between these vertices.
 *
 * @param g      the graph in which the selection is done
 * @param eid    identifier of the edge with label
 * @param label  label of the predicate
 * @param args   nodes used as argument of the predicate
 * @param used   set of already used edges of g2
 */
noll_graph_t *
noll_graph_select_ls (noll_graph_t * g, uint_t eid, uint_t label,
		      noll_uid_array * args, noll_uid_array * used)
{
  /* pre-conditions */
  assert (g != NULL);
  /* - valid predicate label */
  assert (label < noll_vector_size (preds_array));
  /* - valid predicate arguments */
  assert (args != NULL);
  // TODO: pargs is not correctly filled
  // assert (noll_vector_size(args) == noll_vector_at(preds_array,label)->def->pargs);
  /* - valid used set */
  assert (used != NULL);
  assert (noll_vector_size (used) == noll_vector_size (g->edges));

#ifndef NDEBUG
  fprintf (stdout, "select_ls: for predicate %d\n", label);
#endif

  /*
   * Allocate the result
   */
  noll_graph_t *rg = noll_graph_copy_nodes (g);

  /*
   * Build the set of nodes vg
   */
  /* bit set of nodes in @p g selected */
  uint_t vg_size = g->nodes_size;
  int *vg = (int *) malloc (vg_size * sizeof (int));
  for (uint_t i = 0; i < vg_size; i++)
    vg[i] = -1;		/* not marked */
  /* mark the starting node */
  vg[noll_vector_at (args, 0)] = 0;	/* starting */
  /* mark the ending node */
  vg[noll_vector_at (args, 1)] = 1;	/* ending */
  /* mark the border nodes */
  for (uint_t i = 2; i < noll_vector_size (args); i++)
  {
    uid_t ai = noll_vector_at (args, i);
    if (vg[ai] == -1)
      // only boder arguments that are not already start and end
      vg[ai] = 3;	/* border */
  }
  /* the queue of nodes to be explored */
  noll_uid_array *vqueue = noll_uid_array_new ();
  noll_uid_array_push (vqueue, noll_vector_at (args, 0));
  /* sets also the edges explored and labeled in L2 */
  uint_t eg_size = noll_vector_size (g->edges);
  int *eg = (int *) malloc (eg_size * sizeof (int));
  for (uint_t i = 0; i < eg_size; i++)
    eg[i] = 0;			/* not marked */
  /* exploration */
  while (noll_vector_size (vqueue) >= 1)
    {
      uint_t v = noll_vector_last (vqueue);
      noll_uid_array_pop (vqueue);
      /* test that there is not an already marked node */
      /* TODO: last condition is to deal with dll,
       * better condition */
      if (vg[v] >= 2 ||
          (vg[v] == 1 && (noll_pred_is_one_dir(label) == false)))
	{
	  /* mark it again as explored */
	  vg[v] = 2;
	}
      else
	{
	  /* mark the node */
	  vg[v] = 2;		/* internal */
	  /* look at its successors labeled in L2 */
	  noll_uid_array *out_v = g->mat[v];
	  if (out_v != NULL)
	    {
	      for (uint_t i = 0; i < noll_vector_size (out_v); i++)
		{
		  uint_t ei = noll_vector_at (out_v, i);
		  /* if this edge has been already used, then error and stop */
		  if (noll_vector_at (used, ei) != UNDEFINED_ID)
		    {
		      fprintf (stdout,
			       "select_ls: Explored edge already used (1)!\n");
		      goto return_select_ls_error;
		    }
		  noll_edge_t *e = noll_vector_at (g->edges, ei);
		  /* if the label is in the L2 set,
		   * then add the successors to the queue */
		  if (!noll_edge_in_label (e, label))
		    continue;	/* the for loop */
		  eg[ei] = 1;
		  /* insert the destination and the border nodes into the queue */
		  for (uint_t p = 1; p < noll_vector_size (e->args); p++)
		    {
		      noll_uid_array_push (vqueue,
					   noll_vector_at (e->args, p));
		    }
		}
	    }
	}
    }
  noll_uid_array_delete (vqueue);

#ifndef NDEBUG
  fprintf (stdout, "\t- exploration done, check arguments\n");
#endif

  /* check that all arguments have been explored */
  for (uint_t i = 0; i < noll_vector_size (args); i++)
    {
      if (vg[noll_vector_at (args, i)] != 2)
	{
	  fprintf (stdout, "select_ls: %dth argument unexplored!\n", i);
	  goto return_select_ls_error;
	}
    }
  /* redo marking of border arguments */
  vg[noll_vector_at (args, 0)] = 0;
  vg[noll_vector_at (args, 1)] = 1;
  for (uint_t i = 2; i < noll_vector_size (args); i++)
     if (vg[noll_vector_at (args, i)] == 2)
       vg[noll_vector_at (args, i)] = 3;

#ifndef NDEBUG
  fprintf (stdout, "\t- mark used edges, build the graph\n");
#endif

  /*
   * Mark the edges outgoing from vg (except from border) as used.
   * Insert the edges labeled by labels in L2 in the result.
   */
  for (uint_t v = 0; v < vg_size; v++)
    {
      if (vg[v] >= 0 && vg[v] <= 2)
	{
	  /* outgoing edges from i */
	  noll_uid_array *out_v = g->mat[v];
	  if (out_v != NULL)
	    {
	      for (uint_t i = 0; i < noll_vector_size (out_v); i++)
		{
		  uint_t ei = noll_vector_at (out_v, i);
		  if (noll_vector_at (used, ei) != UNDEFINED_ID)
		    {
		      fprintf (stdout,
			       "select_ls: Explored edge already used (2)!\n");
		      goto return_select_ls_error;
		    }
		  noll_vector_at (used, ei) = eid;
		  if (eg[eid] == 1)
		    {
		      noll_edge_t *e = noll_vector_at (g->edges, ei);
		      /* edge using the label, copy in the result */
		      noll_edge_t *ecopy = noll_edge_copy (e);
		      /* the source node */
		      uint_t src = noll_vector_at (ecopy->args, 0);
		      /* the destination node */
		      uint_t dst = noll_vector_at (ecopy->args, 1);
		      /* the edge index */
		      uint_t new_id = noll_vector_size (rg->edges);
		      noll_edge_array_push (rg->edges, ecopy);
		      ecopy->id = new_id;
		      /* update the the adjacency matrices */
		      if (rg->mat[src] == NULL)
			rg->mat[src] = noll_uid_array_new ();
		      noll_uid_array_push (rg->mat[src], new_id);
		      if (rg->rmat[dst] == NULL)
			rg->rmat[dst] = noll_uid_array_new ();
		      noll_uid_array_push (rg->rmat[dst], new_id);
		    }
		}
	    }
	}
    }

#ifndef NDEBUG
  fprintf (stdout, "\t- insert difference edges inside the graph selected\n");
#endif

  /*
   * Insert the difference edges between the marked vertices.
   */
  for (uint_t i = 0; i < vg_size; i++)
    {
      for (uint_t j = 0; j <= i; j++)
	{
	  if (vg[i] >= 0 && vg[j] >= 0)
	    rg->diff[i][j] = g->diff[i][j];
	}
    }
  goto return_select_ls;

return_select_ls_error:
  /* redo the used edges */
  for (uint_t v = 0; v < vg_size; v++)
    {
      if (vg[v] >= 0 && vg[v] <= 2)
	{
	  /* outgoing edges from i */
	  noll_uid_array *out_v = g->mat[v];
	  if (out_v != NULL)
	    {
	      for (uint_t i = 0; i < noll_vector_size (out_v); i++)
		{
		  uint_t ei = noll_vector_at (out_v, i);
		  noll_vector_at (used, ei) = UNDEFINED_ID;
		}
	    }
	}
    }
  /* deallocate the result */
  noll_graph_free (rg);
  rg = NULL;

#ifndef NDEBUG
  fprintf (stdout, "\t- return NULL\n");
#endif

return_select_ls:
  /* correct return, free the auxiliary memory */
  if (vg != NULL)
    free (vg);
  if (eg != NULL)
    free (eg);


#ifndef NDEBUG
  fprintf (stdout, "\t- return graph\n");
  noll_graph_fprint (stdout, rg);
#endif

  return rg;
}

/**
 * For the dll edges (labeled by @p pid) in the graph @p g,
 * add a next edge between the target of the edge and the forward argument.
 *
 */
void
noll_graph_dll(noll_graph_t* g, uid_t pid)
{
  assert (NULL != g);

  // get the fields fid_nxt and fid_prv
  uid_t fid_next = UNDEFINED_ID;
  uid_t fid_prev = UNDEFINED_ID;
  noll_pred_t* pred = noll_vector_at(preds_array,pid);
  assert (NULL != pred);
  assert (NULL != pred->typ);
  assert (NULL != pred->typ->pfields);
  for (uint_t fi = 0;
      (fi < noll_vector_size(fields_array)) &&
      (fid_next == UNDEFINED_ID || fid_prev == UNDEFINED_ID);
      fi++)
  {
  if (noll_vector_at(pred->typ->pfields, fi) == NOLL_PFLD_BCKBONE)
    fid_next = fi;
  else if (noll_vector_at(pred->typ->pfields, fi) == NOLL_PFLD_BORDER)
    fid_prev = fi;
  }

  // array of added edges
  noll_edge_array* e1_en = noll_edge_array_new();
  // the first valid identifier for the added edges
  uint_t lst_eid = noll_vector_size(g->edges);
  for (uint ei = 0; ei < noll_vector_size(g->edges); ei++)
  {
    noll_edge_t* e = noll_vector_at(g->edges, ei);
    if (e->kind != NOLL_EDGE_PRED)
      continue;
    uint_t nfst = noll_vector_at(e->args,0);
    uint_t nlst = noll_vector_at(e->args,1);
    uint_t nprv = noll_vector_at(e->args,2);
    uint_t nfwd = noll_vector_at(e->args,3);

    /* edge nlst --next-->nfwd */
    noll_edge_t* enext = noll_edge_alloc(NOLL_EDGE_PTO, nlst, nfwd, fid_next);
    enext->id = lst_eid;
    lst_eid++;
    noll_edge_array_push(e1_en, enext);

    // update matrices of g
    // push the edge enext in the matrix at entry nlst
    noll_uid_array* lst_edges = g->mat[nlst];
    if (lst_edges == NULL) {
    lst_edges = g->mat[nlst] = noll_uid_array_new();
    }
    noll_uid_array_push(lst_edges, enext->id);
    // push the edge enext in the reverse matrix at entry nfwd
    noll_uid_array* fwd_edges = g->rmat[nfwd];
    if (fwd_edges == NULL) {
    fwd_edges = g->rmat[nfwd] = noll_uid_array_new();
    }
    noll_uid_array_push(fwd_edges, enext->id);

    /* edge nfst --prev-->nprev */
    noll_edge_t* eprev = noll_edge_alloc(NOLL_EDGE_PTO, nfst, nprv, fid_prev);
    eprev->id = lst_eid;
    lst_eid ++;
    noll_edge_array_push(e1_en, eprev);

    // push the edge eprev in the matrix at entry nfst
    noll_uid_array* fst_edges = g->mat[nfst];
    if (fst_edges == NULL) {
    fst_edges = g->mat[nfst] = noll_uid_array_new();
    }
    noll_uid_array_push(fst_edges, eprev->id);
    // push the edge eprev in the reverse matrix at entry nprv
    noll_uid_array* prv_edges = g->rmat[nprv];
    if (prv_edges == NULL) {
    prv_edges = g->rmat[nprv] = noll_uid_array_new();
    }
    noll_uid_array_push(prv_edges, eprev->id);
  }
  // push all the added edges in g
  for (uint ei = 0; ei < noll_vector_size(e1_en); ei++)
  {
    noll_edge_t* e = noll_vector_at(e1_en, ei);
    noll_edge_array_push(g->edges, e);
    noll_vector_at(e1_en, ei) = NULL;
  }
  noll_edge_array_delete(e1_en);
}

/**
 * Check that the graph in @p g2 is an unfolding of the edge @p e1.
 * The mapping of the arguments of @p e1 on nodes of @p g2 are given by @p h.
 */
int
noll_graph_shom_entl (noll_graph_t * g2, noll_edge_t * e1, noll_uid_array * h)
{
  /* pre-conditions */
  assert (g2 != NULL);
  assert (e1 != NULL);
  assert (h != NULL);

  /* TODO: select the method of checking entailment using the option */

  /* HERE follows the TA based procedure */
  if (noll_pred_is_one_dir(e1->label) == false)
  {
    // special case for generating TA from graphs with dll
    noll_graph_dll(g2, e1->label);
  }
  noll_ta_t *g2_ta = noll_graph2ta (g2, h);
	if (NULL == g2_ta)
	{	// if the graph could not be translated to a tree
		NOLL_DEBUG("Could not translate the graph into a tree!\n");
		return 0;
	}
#ifndef NDEBUG
  NOLL_DEBUG ("\nGraph TA:\n");
  vata_print_ta (g2_ta);
  NOLL_DEBUG ("\n");
#endif

  noll_ta_t *e1_ta = noll_edge2ta (e1);
  assert (NULL != e1_ta);

#ifndef NDEBUG
  NOLL_DEBUG ("\nEdge TA:\n");
  vata_print_ta (e1_ta);
  NOLL_DEBUG ("\n");
#endif

  bool inclRes = vata_check_inclusion (g2_ta, e1_ta);
  vata_free_ta (g2_ta);
  vata_free_ta (e1_ta);

#ifndef NDEBUG
  NOLL_DEBUG ("\nResult of inclusion check: %d\n", inclRes);
#endif

  return (inclRes) ? 1 : 0;
}

/**
 * Build the ls_hom component of the homomorphism
 * which maps all ls edges in @p g1 to subgraphs in @p g2
 * such that the labeling with fields is respected.
 * Mark the mapped edges of @p g2 in usedg2.
 *
 * The graphs is the @return are subgraphs of g2
 * such that they contain only the edges mapped.
 *
 * @param g1     domain graph for the homomorphism (in)
 * @param g2     co-domain graph (in)
 * @param n_hom  node mapping (in)
 * @return       the mapping built, NULL otherwise
 */
noll_graph_array *
noll_graph_shom_ls (noll_graph_t * g1, noll_graph_t * g2,
		    uint_t * n_hom, noll_uid_array * usedg2)
{
  assert (g1 != NULL);
  assert (g2 != NULL);
  assert (n_hom != NULL);
  assert (usedg2 != NULL);

  /* initialize the result with undefined identifiers */
  noll_graph_array *ls_hom = noll_graph_array_new ();
  noll_graph_array_reserve (ls_hom, noll_vector_size (g1->edges));

  /* Go through the predicate edges of g1 such that
   * edges with greatest predicate are visited first
   */
  /* sort the predicate edges of g1 using insertion sort */
  uint_t sz = noll_vector_size (g1->edges);
  /* the permutation generated by the sorting */
  uint_t *t = (uint_t *) malloc (sizeof (uint_t) * sz);
  for (uint_t i = 0; i < sz; i++)
    t[i] = i;
  for (uint_t i = 1; i < sz; i++)
    {
      for (uint_t j = i; j >= 1; j--)
	{
	  noll_edge_t *eig = noll_vector_at (g1->edges, t[j]);
	  noll_edge_t *eil = noll_vector_at (g1->edges, t[j - 1]);
	  if ((eig->kind == NOLL_EDGE_PTO && eil->kind == NOLL_EDGE_PRED) ||
	      (eig->kind == NOLL_EDGE_PRED && eil->kind == NOLL_EDGE_PRED &&
	       eig->label < eil->label))
	    {
	      // swap values
	      uint_t tmp = t[j - 1];
	      t[j - 1] = t[j];
	      t[j] = tmp;
	    }
	}
    }
  /* Go in the reverse order using t over the predicate edges */
  for (uint_t i = 0; i < sz; i--)
    {
      // the edge to be mapped is at position t[sz - 1 - i]
      uint_t e1id = t[sz - 1 - i];
      noll_edge_t *e1 = noll_vector_at (g1->edges, e1id);
      if (e1->kind == NOLL_EDGE_PTO)
	break;			/* because all PTO edges are at the end */
      /* translate the arguments of e1 using the node morphism */
      /* if predicate uses 'nil' then add nil as last (border) argument */
      noll_uid_array *args2 =
	noll_hom_apply_size_array (n_hom, g1->nodes_size, e1->args,
	noll_pred_use_nil(e1->label));
      /* select the subgraph for edge e1
       * and also set usedg2 with the selected edges */
      noll_graph_t *sg2 =
	noll_graph_select_ls (g2, e1id, e1->label, args2, usedg2);
      if (sg2 == NULL || !noll_graph_shom_entl (sg2, e1, args2))
	{			/* free the allocated memory */
	  noll_graph_array_delete (ls_hom);
	  ls_hom = NULL;
#ifndef NDEBUG
	  fprintf (stdout, "\nshom_ls: fails!\n");
#endif
	  fprintf (stdout, "\nDiagnosis of failure: ");
	  fprintf (stdout, "predicate edge n%d ---%s--> n%d not mapped!\n",
	       noll_vector_at(e1->args,0),
	       noll_pred_name(e1->label),
	       noll_vector_at(e1->args,1));
	  // Warning: usedg2 is deselected also
	  goto return_shom_ls;
	}
      /* otherwise, set the graph in the corresponding entry of ls_hom */
      noll_vector_at (ls_hom, e1id) = sg2;
    }

return_shom_ls:
  free (t);
  return ls_hom;
}

/**
 * Search a homomorphism from noll_prob->ngraph[i] and noll_prob->pgraph.
 * Store the found mapping in hs->shom[i].
 *
 * @param hs   the homomorphism to be built
 * @param i    the source graph to be considered
 * @return     1 if found, -1 if incomplete, 0 otherwise
 */
int
noll_graph_shom (noll_hom_t * hs, size_t i)
{

  /* arguments are correct */
  assert (hs != NULL);
  assert (i < noll_vector_size (noll_prob->ngraph));

  /* fix the graphs to be considered */
  noll_graph_t *g1 = noll_vector_at (noll_prob->ngraph, i);
  noll_graph_t *g2 = noll_prob->pgraph;

  /* Graphs are not empty! */
  assert (g1 != NULL);
  assert (g1->var2node != NULL);
  assert (g1->edges != NULL);
  assert (g2 != NULL);
  assert (g2->var2node != NULL);
  assert (g2->edges != NULL);

  /*
   * Set the result code and hom
   */
  int res = 1;
  uint_t *n_hom = NULL;
  noll_uid_array *usedg2 = NULL;
  noll_uid_array *pto_hom = NULL;
  noll_graph_array *ls_hom = NULL;

  /*
   * Build the mapping of nodes wrt variable labeling,
   * n_hom[n1] = n2 with n1 in g1, n2 in g2, n1, n2 node ids
   */
  n_hom = noll_graph_shom_nodes (g1, g2);
  if (n_hom == NULL)
    {
      res = 0;
      goto return_shom;
    }

  /*
   * While building the mapping for edges,
   * check the separation property of the mapping found
   * (i.e., an edge of g2 is not used in the mapping of two edges in g1)
   * by storing for each edge of g2, the edges of g1 mapped by the hom
   * usedg2[e2] = e1 or UNDEFINED_ID
   * with e2 edge of g2, e1 edge of g1
   */
  usedg2 = noll_uid_array_new ();
  noll_uid_array_reserve (usedg2, noll_vector_size (g2->edges));
  for (uint_t ei2 = 0; ei2 < noll_vector_size (g2->edges); ei2++)
    {
      noll_uid_array_push (usedg2, UNDEFINED_ID);
    }

  /*
   * Build the mapping of points-to edges to points-to edges
   * pto_hom[e1] = e2
   * with ei pto edge in gi, i=1,2
   */
  pto_hom = noll_graph_shom_pto (g1, g2, n_hom, usedg2);
  if (pto_hom == NULL)
    {
      res = 0;
      goto return_shom;
    }

  /*
   * Build the mapping of predicate edges to subgraphs
   * ls_hom[e1] = g2'
   * with e1 predicate edge id in g1,
   *      g2' subgraph of g2
   */
  ls_hom = noll_graph_shom_ls (g1, g2, n_hom, usedg2);
  if (ls_hom == NULL)
    {
      res = 0;
      goto return_shom;
    }

  /*
   * If g1 is precise then all edges in g2 shall be used
   */
  for (uint_t i = 0; i < noll_vector_size (usedg2); i++)
    if (noll_vector_at (usedg2, i) == UNDEFINED_ID)
      {
	res = 0;
	fprintf (stdout, "\nEdge %d of the left graph is not used!", i);
	goto return_shom;
      }

  /* TODO: Add the sharing constraints defined by h to g2,
   * @see noll_graph_homomorphism_old
   */

return_shom:
  /* free allocated memory if the homomorphism can not be built */
  if (res == 0)
    {
      if (n_hom != NULL)
	free (n_hom);
      if (pto_hom != NULL)
	noll_uid_array_delete (pto_hom);
      if (ls_hom != NULL)
	noll_graph_array_delete (ls_hom);
      if (usedg2 != NULL)
	noll_uid_array_delete (usedg2);
    }
  noll_shom_t *h = (noll_shom_t *) malloc (sizeof (noll_shom_t));
  h->ngraph = i;
  h->is_empty = (res == 0) ? true : false;
  h->node_hom = (res == 0) ? NULL : n_hom;
  h->pto_hom = (res == 0) ? NULL : pto_hom;
  h->ls_hom = (res == 0) ? NULL : ls_hom;
  h->pused = (res == 0) ? NULL : usedg2;
  // push hom found in hs
  if (hs->is_empty)
    hs->is_empty = false;
  assert (NULL != hs->shom);
  assert (i < noll_vector_size(hs->shom));
  noll_vector_at(hs->shom,i) = h;

  /* TODO: to be changed for disjunctions */
  return res;
}


/**
 * OLD VERSION.
 * Find a homomorphism for the query q.
 *
 * The following additional actions are done:
 * - maps spatial edges of q->ngraph to subgraphs in q->pgraph,
 * - check the entailment of pure constraints (difference edges),
 * - start checking sharing constraints.
 *
 * If precise=true then it checks the additional conditions
 * required by the precise semantics.
 *
 * @return 1 if homomorphism found, 0 otherwise.
 */
int
noll_graph_homomorphism_old (noll_entl_t * q)
{
  assert (q != NULL);
  noll_graph_t *g1 = noll_vector_at (q->ngraph, 0);
  noll_graph_t *g2 = q->pgraph;

  /* pre-condition: graphs are not empty,
   * special cases have been considered already, @see noll_entl_solve! */
  assert (g1 != NULL);
  assert (g1->var2node != NULL);
  assert (g1->edges != NULL);
  assert (g2 != NULL);
  assert (g2->var2node != NULL);
  assert (g2->edges != NULL);

  /* results */
  int res = 1;
  uint_t *h = NULL;		// for homomorphism
  noll_uid_array *used = NULL;	// for used set
  noll_uid_array **h_edge = NULL;	// for edge mapping

  /*
   * Map all nodes in g1 to nodes in g2 such that labeling with
   * variables is preserved
   */
  h = (uint_t *) malloc (g1->nodes_size * sizeof (uint_t));
  // initialize entries by default
  for (uint_t i = 0; i < g1->nodes_size; i++)
    h[i] = UNDEFINED_ID;
  for (uint_t v = 0; v < noll_vector_size (g1->lvars); v++)
    {
      // TODO: incorrect if local variables, check the variable name
      uint_t n1v = g1->var2node[v];
      uint_t n2v = g2->var2node[v];
      if (n1v != UNDEFINED_ID)
	{
	  if (n2v != UNDEFINED_ID)
	    h[n1v] = n2v;
	  else
	    {
	      res = 0;
	      goto check_hom;
	    }
	}
    }
  // verify that no default value is still in h
  // TODO: what happens with node labeled by local variables
  for (uint_t i = 0; i < g1->nodes_size; i++)
    if (h[i] == UNDEFINED_ID)
      {
	res = 0;
	fprintf (stdout, "Node n%d of right side graph not mapped!", i);
	goto check_hom;
      }

#ifndef NDEBUG
  fprintf (stdout,
	   "Homomorphism built from labeling with program variables:\n\t[");
  for (uint_t i = 0; i < g1->nodes_size; i++)
    fprintf (stdout, "n%d --> n%d, ", i, h[i]);
  fprintf (stdout, "\n");
#endif

  /*
   * Verify difference edges from g1 mapped to diff edges in g2
   */
  for (uint_t ni1 = 1; ni1 < g1->nodes_size; ni1++)
    {
      for (uint_t nj1 = 0; nj1 < ni1; nj1++)
	{
	  if (g1->diff[ni1][nj1])
	    {
	      uint_t ni2 = h[ni1];
	      uint_t nj2 = h[nj1];
	      bool isdiff2 =
		(ni2 < nj2) ? g2->diff[nj2][ni2] : g2->diff[ni2][nj2];
	      if (isdiff2 == false)
		{
		  res = 0;
		  // TODO: put message with program variables
		  fprintf (stdout,
			   "Difference edges (n%d != n%d) in the right side grah ",
			   ni1, nj1);
		  fprintf (stdout,
			   "is not mapped to (n%d != n%d) in the left side graph!\n",
			   ni2, nj2);
		  goto check_hom;
		}
	    }
	}
    }
  // used set, used[ei2 in g2] = ei1 in g1
  // several edges in g2 are needed for list segments
  used = noll_uid_array_new ();
  noll_uid_array_reserve (used, noll_vector_size (g2->edges));
  for (uint_t ei2 = 0; ei2 < noll_vector_size (g2->edges); ei2++)
    {
      noll_uid_array_push (used, UNDEFINED_ID);
    }

  // edge mapping, h_edge[ei1 in g1] = array of edge ids in g2
  h_edge =
    (noll_uid_array **) malloc (noll_vector_size (g1->edges) *
				sizeof (noll_uid_array *));
  for (uint_t ei1 = 0; ei1 < noll_vector_size (g1->edges); ei1++)
    {
      h_edge[ei1] = noll_uid_array_new ();
    }
  /*
   * Verify that edges in g1 may be mapped to (implicit) pto edges in g2
   */
  for (uint_t ei1 = 0; ei1 < noll_vector_size (g1->edges); ei1++)
    {
#ifndef NDEBUG
      fprintf (stdout, "==== Mapping edge %d in g1: \n", ei1);
#endif
      noll_edge_t *edge_i1 = noll_vector_at (g1->edges, ei1);
      // apply the h on the args of this edge
      noll_uid_array *args2 = noll_hom_apply_size_array (h, g1->nodes_size,
							 edge_i1->args,
							 false);
      // search the mapping of ei1 into a (list of) edge(s),
      // by, if needed, saturating g2
      noll_uid_array *lei2 = noll_graph_get_edge (g2, edge_i1->kind, args2,
						  edge_i1->label);

      // if edges has been added in g2, update used
      for (uint_t i = noll_vector_size (used);
	   i < noll_vector_size (g2->edges); i++)
	noll_uid_array_push (used, UNDEFINED_ID);
      if (lei2 != NULL)
	{
#ifndef NDEBUG
	  fprintf (stdout, "---- right edge-%d mapped to left edges-[", ei1);
#endif
	  for (uint_t i2 = 0; i2 < noll_vector_size (lei2); i2++)
	    {
	      uint_t ei2 = noll_vector_at (lei2, i2);
#ifndef NDEBUG
	      fprintf (stdout, "%d,", ei2);
#endif
	      if (noll_graph_used (used, ei2, g2))
		{
		  res = 0;
		  fprintf (stdout, "Edge (left) %d is already used!", ei2);
		  goto check_hom;
		}
	      noll_vector_at (used, ei2) = ei1;
	      noll_uid_array_push (h_edge[ei1], ei2);
	    }
#ifndef NDEBUG
	  fprintf (stdout, "]\n");
#endif
	}
      else
	{
	  res = 0;
	  fprintf (stdout, "---- right edge %d not mapped!", ei1);
	  goto check_hom;
	}

      //if g1 is precise, we need to check that the set of edges lei2 is acyclic
      if (g1->is_precise && (lei2 != NULL))
	if (!noll_graph_check_acyclicity (g2, lei2))
	  {
	    fprintf (stdout,
		     "=== right edge-%d mapped to a set of edges that may contain a cycle\n",
		     ei1);
	    res = 0;
	    goto check_hom;
	  }
    }

  // if g1 is precise check that all edges in g2 are used
  for (uint_t i = 0; i < noll_vector_size (used); i++)
    if (noll_vector_at (used, i) == UNDEFINED_ID)
      {
	res = 0;
	fprintf (stdout, "Edge (left) %d not used!", i);
	goto check_hom;
      }

  /*
   * Verify that the separation constraints are satisfied by the edge mapping, i.e.,
   * for any edge e1i in g1 strong separated from e1j then
   *     h_edge[e1i] are all strong separated from h_edge[e1j]
   */
  for (uint_t ei1 = 0; ei1 < noll_vector_size (g1->edges); ei1++)
    {
      // the edge in g1
      noll_edge_t *edge_i1 = noll_vector_at (g1->edges, ei1);
      // the mapped edges in g2
      noll_uid_array *lei2 = h_edge[ei1];
      assert (lei2 != NULL);
      assert (noll_vector_size (lei2) >= 1);
      // go through the separated edges from ei1 in g1
      for (uint_t j1 = 0; j1 < noll_vector_size (edge_i1->ssep); j1++)
	{
	  uint_t ej1 = noll_vector_at (edge_i1->ssep, j1);
	  // ej1 is mapped to edges in g2
	  noll_uid_array *lej2 = h_edge[ej1];
	  assert (lej2 != NULL);
	  assert (noll_vector_size (lej2) >= 1);
	  // TODO: improve complexity here by sorting the arrays of ssep
	  // for each edge in lei2, check that its separation set includes lej2
	  for (uint_t i2 = 0; i2 < noll_vector_size (lei2); i2++)
	    {
	      uint_t ei2 = noll_vector_at (lei2, i2);
	      noll_uid_array *ssepi2 = noll_vector_at (g2->edges, ei2)->ssep;
	      for (uint_t j2 = 0; j2 < noll_vector_size (lej2); j2++)
		{
		  uint_t ej2 = noll_vector_at (lej2, j2);
		  bool found = false;
		  for (uint_t si2 = 0; si2 < noll_vector_size (ssepi2)
		       && !found; si2++)
		    {
		      uint_t sei2 = noll_vector_at (ssepi2, si2);
		      if (ej2 == sei2)
			found = true;
		    }
		  if (!found)
		    {
		      res = 0;
		      fprintf (stdout,
			       "Mapping of edges (right) %d --> (left) %d",
			       ei1, ei2);
		      fprintf (stdout,
			       " does not respect separation from edge (right) %d --> (left) %d!",
			       ej1, ej2);
		      goto check_hom;
		    }
		}
	    }
	}
    }

  /* if the homomorphism exists then
   * add the sharing constraints defined by h to g2
   */
  if (h_edge != NULL)
    {
      for (uint_t ei1 = 0; ei1 < noll_vector_size (g1->edges); ei1++)
	{
	  noll_edge_t *e1 = noll_vector_at (g1->edges, ei1);
	  noll_sterm_t *sterm_e1 = NULL;	// term built for this edge
	  if (e1->kind == NOLL_EDGE_PRED)
	    {
	      // get its set variable
	      uint_t svar_e1 = e1->bound_svar;
	      sterm_e1 = noll_sterm_new_var (svar_e1, NOLL_STERM_SVAR);
	    }
	  else if (e1->kind == NOLL_EDGE_PTO)
	    {
	      // get its location variable (node)
	      uint_t node_e1 = noll_vector_at (e1->args, 0);
	      uint_t var_e1 = noll_graph_get_var (g1, node_e1);
	      sterm_e1 = noll_sterm_new_var (var_e1, NOLL_STERM_LVAR);
	    }
	  else
	    assert (0);
	  // build the term from h_edge[e1]
	  noll_sterm_array *sterm_h_e1 = noll_sterm_array_new ();
	  for (uint_t ei2 = 0; ei2 < noll_vector_size (h_edge[ei1]); ei2++)
	    {
	      noll_edge_t *e2 = noll_vector_at (g2->edges, ei2);
	      noll_sterm_t *sterm_e2 = NULL;
	      if (e2->kind == NOLL_EDGE_PRED)
		sterm_e2 = noll_sterm_new_var (e2->bound_svar,
					       NOLL_STERM_SVAR);
	      else if (e2->kind == NOLL_EDGE_PTO)
		sterm_e2 = noll_sterm_new_var (noll_vector_at (e2->args, 0),
					       NOLL_STERM_LVAR);
	      else
		assert (0);
	      // push constraint sterm_e2 <= sterm_e1
	      noll_atom_share_t *e2_in_e1 =
		(noll_atom_share_t *) malloc (sizeof (noll_atom_share_t));
	      e2_in_e1->kind = NOLL_SHARE_SUBSET;
	      e2_in_e1->t_left = noll_sterm_copy (sterm_e2);
	      e2_in_e1->t_right = noll_sterm_array_new ();
	      noll_sterm_array_push (e2_in_e1->t_right,
				     noll_sterm_copy (sterm_e1));
	      noll_share_array_push (g2->share, e2_in_e1);
	      // push term sterm_e2 in sterm_h_e1
	      noll_sterm_array_push (sterm_h_e1, sterm_e2);
	    }
	  // push constraint sterm_e1 <= sterm_h_e1
	  noll_atom_share_t *e1_in_h_e1 =
	    (noll_atom_share_t *) malloc (sizeof (noll_atom_share_t));
	  e1_in_h_e1->kind = NOLL_SHARE_SUBSET;
	  e1_in_h_e1->t_left = sterm_e1;
	  e1_in_h_e1->t_right = sterm_h_e1;
	  noll_share_array_push (g2->share, e1_in_h_e1);
	}
    }

check_hom:if (h != NULL)
    free (h);
  if (used != NULL)
    {
      noll_uid_array_delete (used);
    }
  if (h_edge != NULL)
    {
      for (uint_t ei1 = 0; ei1 < noll_vector_size (g1->edges); ei1++)
	{
	  noll_uid_array_delete (h_edge[ei1]);
	}
      free (h_edge);
    }
  return res;
}
