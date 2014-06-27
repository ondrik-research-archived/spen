/**************************************************************************/
/*                                                                        */
/*  SPEN decision procedure                                               */
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
 * Graph representation of NOLL formulas.
 */

#include "noll_types.h"
#include "noll_form.h"
#include "noll_graph.h"

NOLL_VECTOR_DEFINE (noll_edge_array, noll_edge_t *);

NOLL_VECTOR_DEFINE (noll_graph_array, noll_graph_t *);

/* ====================================================================== */
/* Constructors/destructors */
/* ====================================================================== */

noll_edge_t *
noll_edge_alloc (noll_edge_e kind, uint_t src, uint_t dst, uint_t label)
{
  noll_edge_t *e = (noll_edge_t *) malloc (sizeof (noll_edge_t));
  e->kind = kind;
  e->label = label;
  e->args = noll_uid_array_new ();
  noll_uid_array_push (e->args, src);
  noll_uid_array_push (e->args, dst);
  e->id = UNDEFINED_ID;
  e->bound_svar = UNDEFINED_ID;
  ;                             // index of the set variable in slocs_array bounded to the edge, or UNDEFINED_ID
  e->impl = NULL;
  e->ssep = noll_uid_array_new ();
  return e;
}

void
noll_edge_free (noll_edge_t * e)
{
  if (e == NULL)
    return;
  if (e->args != NULL)
    {
      noll_uid_array_delete (e->args);
      e->args = NULL;
    }
  if (e->impl != NULL)
    {
      noll_uid_array_delete (e->impl);
      e->impl = NULL;
    }
  if (e->ssep != NULL)
    {
      noll_uid_array_delete (e->ssep);
      e->ssep = NULL;
    }
  free (e);
}

noll_edge_t *
noll_edge_copy (noll_edge_t * e)
{
  /* pre-conditions */
  assert (e != NULL);

  uint_t src = noll_vector_at (e->args, 0);
  uint_t dst = noll_vector_at (e->args, 1);
  noll_edge_t *re = noll_edge_alloc (e->kind, src, dst, e->label);
  /* push the other arguments if there exists */
  for (uint_t i = 2; i < noll_vector_size (e->args); i++)
    noll_uid_array_push (re->args, noll_vector_at (e->args, i));
  /* TODO: fill the informations for overlapping */

  return re;
}

/**
 * Allocate a graph using the informations about the formula.
 * If nodes==0 or edges==0, return the  empty graph, i.e.,
 * only nil node.
 */
noll_graph_t *
noll_graph_alloc (noll_var_array * lvars, noll_var_array * svars,
                  uint_t nodes, uint_t edges, uint_t * vars)
{

  noll_graph_t *res = (noll_graph_t *) malloc (sizeof (noll_graph_t));
  res->lvars = noll_var_array_new ();
  noll_var_array_copy (res->lvars, lvars);
  res->svars = noll_var_array_new ();
  noll_var_array_copy (res->svars, svars);
  // size of the adj matrices
  res->nodes_size = nodes;
  /*
   * labeling of nodes by variables: fill mapping var2nodes
   */
  if (!vars)
    {
      res->var2node = (uint_t *) malloc (noll_vector_size (lvars)
                                         * sizeof (uint_t));
      for (uint_t i = 0; i < noll_vector_size (lvars); i++)
        res->var2node[i] = UNDEFINED_ID;
    }
  else
    res->var2node = vars;
  /*
   * allocate the array of edges
   */
  res->edges = noll_edge_array_new ();
  if (edges > 0)
    noll_edge_array_reserve (res->edges, edges);

  /*
   * allocate the adjacency matrices
   */
  res->mat = (noll_uid_array **) malloc (res->nodes_size
                                         * sizeof (noll_uid_array *));
  res->rmat = (noll_uid_array **) malloc (res->nodes_size
                                          * sizeof (noll_uid_array *));
  for (uint_t i = 0; i < res->nodes_size; i++)
    {
      res->mat[i] = NULL;
      res->rmat[i] = NULL;
    }

  /*
   * allocate the difference edges, a low-diagonal matrix
   */
  res->diff = (bool **) malloc (res->nodes_size * sizeof (bool *));
  for (uint_t i = 0; i < res->nodes_size; i++)
    {
      res->diff[i] = (bool *) malloc ((i + 1) * sizeof (bool));
      for (uint_t j = 0; j <= i; j++)
        res->diff[i][j] = false;
    }
  /*
   *  allocate the mapping of set variables to edges
   */
  res->sloc2edge =
    (uint_t *) malloc (noll_vector_size (svars) * sizeof (uint_t));
  for (uint_t i = 0; i < noll_vector_size (svars); i++)
    {
      res->sloc2edge[i] = UNDEFINED_ID;
    }
  // allocate the sharing array
  res->share = noll_share_array_new ();

  res->isComplete = false;
  return res;
}

void
noll_graph_free (noll_graph_t * g)
{

  noll_var_array_delete (g->lvars);
  g->lvars = NULL;
  noll_var_array_delete (g->svars);
  g->svars = NULL;
  if (g->var2node != NULL)
    free (g->var2node);
  for (uint_t i = 0; i < g->nodes_size; i++)
    {
      if (g->mat[i] != NULL)
        noll_uid_array_delete (g->mat[i]);
      if (g->rmat[i] != NULL)
        noll_uid_array_delete (g->rmat[i]);
    }
  free (g->mat);
  free (g->rmat);
  noll_edge_array_delete (g->edges);
  if (g->diff != NULL)
    for (uint_t i = 0; i < g->nodes_size; i++)
      {
        free (g->diff[i]);
      }
  free (g->diff);
  if (g->sloc2edge != NULL)
    free (g->sloc2edge);
  if (g->share != NULL)
    noll_share_array_delete (g->share);
  free (g);
}

/**
 * Copy only node informations.
 */
noll_graph_t *
noll_graph_copy_nodes (noll_graph_t * g)
{
  if (g == NULL)
    return NULL;

  uint_t v_sz = noll_vector_size (g->lvars);
  uint_t e_sz = noll_vector_size (g->edges);

  noll_graph_t *rg = noll_graph_alloc (g->lvars, g->svars, g->nodes_size,
                                       e_sz, NULL);

  /* copy var2nodes */
  uint_t *v2n = (uint_t *) malloc (sizeof (uint_t) * v_sz);
  for (uint_t i = 0; i < v_sz; i++)
    rg->var2node[i] = g->var2node[i];

  rg->isComplete = g->isComplete;
  rg->is_precise = g->is_precise;

  return rg;
}


/* ====================================================================== */
/* Getters/setters */
/* ====================================================================== */

uint_t
noll_graph_get_var (noll_graph_t * g, uint_t n)
{
  for (uint_t vi = 0; vi < noll_vector_size (g->lvars); vi++)
    if (g->var2node[vi] == n)
      return vi;
  return UNDEFINED_ID;
}

/** 
 * Test if the edge @p e has its label in the set of labels 
 * of the predicate @p pid. 
 * @param e     edge to be tested
 * @param pid   index of a predicate in preds_array
 * @return      1 if test successful, 0 otherwise
 */
int
noll_edge_in_label (noll_edge_t * e, uint_t pid)
{
  /* pre-conditions */
  assert (e != NULL);
  assert (pid < noll_vector_size (preds_array));

  /* the fields of label are defined in its binding */
  const noll_pred_t *pred = noll_pred_getpred (pid);
  noll_pred_typing_t *pdef = pred->typ;
  int res = 0;
  if (e->kind == NOLL_EDGE_PTO)
    {
      if (noll_pred_is_field (pid, e->label, NOLL_PFLD_NESTED))
        res = 1;
    }
  else
    {
      /* it is a predicate edge */
      if (pid == e->label)
        {                       /* it is the same predicate */
          res = 1;
        }
      else
        {
          /* it is an inner predicate */
          if (pdef->ppreds != NULL)
            {
              for (uint_t i = 0;
                   (res == 0) && i < noll_vector_size (pdef->ppreds); i++)
                {
                  uint_t pi = noll_vector_at (pdef->ppreds, i);
                  if (pi == e->label)
                    res = 1;
                }
            }
          else
            {
#ifndef NDEBUG
              fprintf (stderr,
                       "noll_edge_in_label: predcate edge not in ppreds null\n");
#endif
              res = 0;
            }
        }
    }
  return res;
}

/* ====================================================================== */
/* Printing */
/* ====================================================================== */

void
noll_edge_fprint (FILE * f, noll_var_array * svars, noll_edge_t * e)
{
  assert (f);
  assert (e);
  assert (e->args);
  switch (e->kind)
    {
    case NOLL_EDGE_PTO:
      {
        fprintf (f, "%d: n%d.f%d==n%d", e->id, noll_vector_at (e->args, 0),
                 e->label, noll_vector_at (e->args, 1));
        break;
      }
    case NOLL_EDGE_PRED:
      {
        char *svarname = (e->bound_svar < noll_vector_size (svars)) ?
          noll_vector_at (svars, e->bound_svar)->vname : "";
        fprintf (f, "%d: %s_%s(n%d,n%d", e->id, noll_pred_name (e->label),
                 svarname,
                 noll_vector_at (e->args, 0), noll_vector_at (e->args, 1));
        if (e && e->args)
          for (uint_t i = 2; i < noll_vector_size (e->args); i++)
            fprintf (f, ",n%d", noll_vector_at (e->args, i));
        fprintf (f, ")");
        break;
      }
    default:
      {
        fprintf (f, "%d: error", e->id);
        break;
      }
    }
}

void
noll_edge_fprint_dot (FILE * f, noll_var_array * svars, noll_edge_t * e)
{
  assert (f);
  assert (e);
  assert (e->args);
  fprintf (f, "n%d -> n%d [label=\"", noll_vector_at (e->args, 0),
           noll_vector_at (e->args, 1));
  noll_edge_fprint (f, svars, e);
  fprintf (f, "\"];\n");
}

void
noll_share_fprint_dot (FILE * f, noll_var_array * lvars,
                       noll_var_array * svars, noll_share_array * phi)
{
  if (!phi)
    {
      fprintf (f, "null");
      return;
    }
  for (uint_t i = 0; i < noll_vector_size (phi); i++)
    {
      noll_share_atom_fprint (f, lvars, svars, noll_vector_at (phi, i));
      fprintf (f, " | ");
    }
  fprintf (f, " true");
  ;
}

void
noll_graph_fprint (FILE * f, noll_graph_t * g)
{
  assert (f);
  if (!g)
    {
      fprintf (f, "\tnull graph\n");
      return;
    }
  fprintf (f, "Graph nodes size: %d\n", g->nodes_size);

  fprintf (f, "Graph nodes labels:\n");
  for (uint_t i = 0; i < noll_vector_size (g->lvars); i++)
    fprintf (f, "%s(n%d),", noll_var_name (g->lvars, i, NOLL_TYP_RECORD),
             g->var2node[i]);
  fprintf (f, "\n");

  fprintf (f, "Graph difference edges: \n");
  assert (g->diff != NULL);
  // low-diagonal matrix
  for (uint_t i = 0; i < g->nodes_size; i++)
    for (uint_t j = 0; j <= i; j++)
      if (g->diff[i][j] == true)
        fprintf (f, "\t\tn%d != n%d\n", i, j);

  fprintf (f, "Graph edges: \n");
  assert (g->edges);
  for (uint_t eid = 0; eid < noll_vector_size (g->edges); eid++)
    {
      noll_edge_fprint (f, g->svars, noll_vector_at (g->edges, eid));
      fprintf (f, "\n");
    }
#ifndef NDEBUG
  fprintf (f, "Matrices: mat = [");
  for (uint_t vi = 0; vi < g->nodes_size; vi++)
    {
      if (g->mat[vi] != NULL)
        {
          fprintf (f, "\n\tn%d --> ", vi);
          for (uint_t i = 0; i < noll_vector_size (g->mat[vi]); i++)
            fprintf (f, "e%d, ", noll_vector_at (g->mat[vi], i));
        }
      if (g->rmat[vi] != NULL)
        {
          fprintf (f, "\n\tn%d <-- ", vi);
          for (uint_t i = 0; i < noll_vector_size (g->rmat[vi]); i++)
            fprintf (f, "e%d, ", noll_vector_at (g->rmat[vi], i));
        }
    }
  fprintf (f, "\n");
#endif
  fprintf (f, "Graph sharing constraints: \n");
  if (g->share)
    {
      noll_share_fprint (f, g->lvars, g->svars, g->share);
    }
  else
    fprintf (f, "\t\tnull\n");

}

void
noll_graph_fprint_dot (char *fname, noll_graph_t * g)
{
  assert (fname);
  if (!g)
    {
      fprintf (stderr, "null graph");
      return;
    }
  FILE *f = fopen (fname, "w");
  if (!f)
    {
      fprintf (stderr, "File %s not found! quit.", fname);
      return;
    }
  fprintf (f, "digraph %s {\nnode [shape=record];\n", fname);
  // print nodes
  for (uint_t n = 0; n < g->nodes_size; n++)
    {
      // print node n with its labels
      fprintf (f, "\tn%d [label=\"{n%d|", n, n);
      for (uint_t v = 0; v < noll_vector_size (g->lvars); v++)
        if (g->var2node[v] == n)
          fprintf (f, "%s ", noll_var_name (g->lvars, v, NOLL_TYP_RECORD));

      fprintf (f, "}\"];\n");
    }
  // print edges

  // fprintf(f, "Graph difference edges: \n");
  assert (g->diff != NULL);
  // low-diagonal matrix
  for (uint_t i = 0; i < g->nodes_size; i++)
    for (uint_t j = 0; j <= i; j++)
      if (g->diff[i][j] == true)
        fprintf (f, "n%d -> n%d [style=dotted];\n", i, j);

  //fprintf(f, "Graph edges: \n");
  assert (g->edges);
  for (uint_t eid = 0; eid < noll_vector_size (g->edges); eid++)
    {
      noll_edge_fprint_dot (f, g->svars, noll_vector_at (g->edges, eid));
      fprintf (f, "\n");
    }

  fprintf (f, "\tshare [label=\"{share|");
  if (g->share)
    {
      noll_share_fprint_dot (f, g->lvars, g->svars, g->share);
    }
  else
    fprintf (f, "\t\tnull\n");
  fprintf (f, "}\"];\n");

  fprintf (f, "\n}\n");
  fflush (f);
  fclose (f);
  return;
}
