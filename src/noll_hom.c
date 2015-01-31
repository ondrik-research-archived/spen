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
 * Homeomorphism definition and computation.
 */

#include <stdbool.h>
#include "noll_option.h"
#include "noll_types.h"
#include "noll_lemma.h"
#include "noll_hom.h"
#include "noll_entl.h"
#include "noll.h"
#include "noll_graph2ta.h"
#include "noll_pred2ta.h"
#include "noll_tree.h"

NOLL_VECTOR_DEFINE (noll_shom_array, noll_shom_t *);

/* ====================================================================== */
/* Constructors/destructors */
/* ====================================================================== */

/**
 * @brief Allocate a homeomorphism for the crt problem. 
 */
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

/** 
 * @brief Free the homeomorphism for the crt problem. 
 */
void
noll_hom_delete (noll_hom_t * h)
{
  if (NULL == h)
    return;

  if (h->shom != NULL)
    noll_shom_array_delete (h->shom);
  free (h);
  return;
}

/**
 * @brief Alocate a map and initialize elements to UNDEFINED_ID.
 */
noll_uid_map *
noll_uid_map_new (uint_t size)
{
  noll_uid_array *res = noll_uid_array_new ();
  if (size != 0)
    {
      noll_uid_array_reserve (res, size);
      for (uint_t i = 0; i < size; i++)
        noll_uid_array_push (res, UNDEFINED_ID);
    }
  return res;
}

/**
 * @brief Free the map.
 */
void
noll_uid_map_delete (noll_uid_map * m)
{
  if (m == NULL)
    return;
  noll_uid_array_delete (m);
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

      if (shi->node_hom == NULL)
        {
#ifndef NDEBUG
          fprintf (f, "NULL\n");
#endif
          continue;
        }

      /* print node mapping */
      if (isempty)
        {
          fprintf (f, "[\n");
          isempty = false;
        }
      fprintf (f, "Simple Homomorphism %d for graph-n%zu: \n", i,
               shi->ngraph);
      fprintf (f, "\tNode mapping (graph-n%d --> graph-p): ", i);
      fprintf (f, "[");
      for (uint_t j = 0; j < ngi->nodes_size; j++)
        fprintf (f, "n%d --> n%d,", j, shi->node_hom[j]);
      fprintf (f, "]");

      /* print edge mapping */
      fprintf (f, "\n\tEdge mapping (graph-p --> graph-n%d): ", i);
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

void
noll_uid_map_fprint (FILE * f, noll_uid_map * h)
{
  assert (NULL != f);
  if (NULL == h)
    {
      fprintf (f, "(null)");
      return;
    }
  fprintf (f, "[");
  for (uint_t i = 0; i < noll_vector_size (h); i++)
    fprintf (f, "%d -> %d,", i, noll_vector_at (h, i));
  fprintf (f, "]");
}

/* ====================================================================== */
/* Solver */
/* ====================================================================== */

/**
 * Return the image of args by the mapping h of size size.
 * Add 'nil' at the end if the predicate used 'nil'.
 */
noll_uid_array *
noll_uid_map_apply (noll_uid_map * h, noll_uid_array * args, bool useNil)
{
  noll_uid_array *res = noll_uid_array_new ();
  uint_t sz = noll_vector_size (args);
  noll_uid_array_reserve (res, sz);
  for (uint_t i = 0; i < noll_vector_size (args); i++)
    {
      uint_t n1 = noll_vector_at (args, i);
      if (n1 >= noll_vector_size (h))
        {
          noll_uid_array_delete (res);
          res = NULL;
          return res;
        }
      uint_t n2 = noll_vector_at (h, n1);
      noll_uid_array_push (res, n2);
    }
  if (useNil)
    {
      /* add nil at the end of args */
      assert (noll_vector_at (h, 0) == 0);      // TODO: check that nil node is always 0
      noll_uid_array_push (res, noll_vector_at (h, 0));
    }
  return res;
}

int noll_shom_build (noll_hom_t * h, size_t i);

/**
 * Search a homeomorphism to prove noll_prob.
 * Store the homeomorphism found in noll_prob->hom.
 * @return 1 if hom found, < 1 otherwise
 */
int
noll_hom_build (void)
{

  assert (noll_prob != NULL);

  /* allocate the homeomorphism */
  noll_hom_t *h = noll_hom_alloc ();

  /* compute a simple homeomorphism for each negative graph */
  int res = 0;
  for (size_t i = 0; i < noll_vector_size (noll_prob->ngraph); i++)
    {
      res = noll_shom_build (h, i);
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
 * @param g1  domain graph for the homeomorphism
 * @param g2  co-domain graph
 * @return    the mapping built, NULL otherwise
 */
noll_uid_map *
noll_shom_build_nodes (noll_graph_t * g1, noll_graph_t * g2)
{
  assert (g1 != NULL);
  assert (g2 != NULL);

  int res = 1;
  noll_uid_map *n_hom = NULL;
  n_hom = noll_uid_map_new (g1->nodes_size);
  /* initialize entries with the default value */
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
            noll_uid_array_set (n_hom, n1v, n2v);
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
    if (noll_vector_at (n_hom, i) == UNDEFINED_ID)
      {
        res = 0;
        fprintf (stdout, "Node n%d of right side graph not mapped!", i);
        goto return_shom_nodes;
      }

#ifndef NDEBUG
  fprintf (stdout,
           "homeomorphism built from the labeling with program variables:\n\t");
  noll_uid_map_fprint (stdout, n_hom);
  fprintf (stdout, "\n");
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
              uint_t ni2 = noll_vector_at (n_hom, ni1);
              uint_t nj2 = noll_vector_at (n_hom, nj1);
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
      noll_uid_map_delete (n_hom);
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
 * @param g1     domain graph for the homeomorphism
 * @param g2     co-domain graph
 * @param n_hom  node mapping
 * @return       the mapping built, NULL otherwise
 */
noll_uid_array *
noll_shom_build_pto (noll_graph_t * g1, noll_graph_t * g2,
                     noll_uid_map * n_hom, noll_uid_array * usedg2)
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
      uint_t nsrc_e2 = noll_vector_at (n_hom, nsrc_e1);
      uint_t ndst_e2 = noll_vector_at (n_hom, ndst_e1);
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
          if (noll_option_is_diag () == true)
            {
              /* failure */
              fprintf (stdout, "\nDiagnosis of failure: ");
              fprintf (stdout,
                       "\n\tConstraint not entailed: %s |--> { .. (%s,%s) .. }\n",
                       noll_var_name (g2->lvars, nsrc_e1, NOLL_TYP_RECORD),
                       noll_field_name (e1->label), noll_var_name (g2->lvars,
                                                                   ndst_e1,
                                                                   NOLL_TYP_RECORD));
            }
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
 * Then, edges outgoing from Vg \ args[1..] (border) are all marked
 * as used (even not labeled by labels in L2) because they cannot be
 * used by another predicate (from the * semantics).
 * The subgraph g2 is defined as the set of edges labeled with L2
 * and outgoing from Vg \ args[1..], and the set of difference edges
 * between these vertices.
 *
 * @param g      the graph in which the selection is done
 * @param eid    identifier of the edge with label
 * @param label  label of the predicate
 * @param args   nodes used as argument of the predicate
 * @param used   set of already used edges of g2
 */
noll_graph_t *
noll_shom_select_rd (noll_graph_t * g, uint_t eid, uint_t label,
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
    vg[i] = -1;                 /* not marked */
  /* mark the starting node */
  vg[noll_vector_at (args, 0)] = 0;     /* starting */
  /* mark the ending node */
  vg[noll_vector_at (args, 1)] = 1;     /* ending */
  /* mark the border nodes */
  for (uint_t i = 2; i < noll_vector_size (args); i++)
    {
      uid_t ai = noll_vector_at (args, i);
      if (vg[ai] == -1)
        // only boder arguments that are not already start and end
        vg[ai] = 3;             /* border */
    }
  /* the queue of nodes to be explored */
  noll_uid_array *vqueue = noll_uid_array_new ();
  noll_uid_array_push (vqueue, noll_vector_at (args, 0));
  /* sets also the edges explored and labeled in L2 */
  uint_t eg_size = noll_vector_size (g->edges);
  int *eg = (int *) malloc (eg_size * sizeof (int));
  for (uint_t i = 0; i < eg_size; i++)
    eg[i] = 0;                  /* not marked */
  /* exploration */
  while (noll_vector_size (vqueue) >= 1)
    {
      uint_t v = noll_vector_last (vqueue);
      noll_uid_array_pop (vqueue);
      /* test that there is not an already marked node */
      if ((vg[v] >= 1 && noll_pred_is_one_dir (label)) ||
          (vg[v] >= 2 && (noll_pred_is_one_dir (label) == false)))
        {
          /* mark it again as explored */
          vg[v] = 2;
        }
      else
        {
          /* mark the node */
          vg[v] = 2;            /* internal */
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
                    continue;   /* the for loop */
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
      uint_t ni = noll_vector_at (args, i);
      uint_t vi = noll_graph_get_var (g, ni);
      noll_type_t *ty_i = NULL;
      if (vi != UNDEFINED_ID)
        ty_i = noll_var_type (g->lvars, vi);
      if ((vg[noll_vector_at (args, i)] != 2) &&
          (ty_i != NULL) && (noll_type_get_record (ty_i) != UNDEFINED_ID))
        {
          fprintf (stdout, "select_ls: argument %d unexplored!\n", i);
          goto return_select_ls_error;
        }
      else if ((ty_i != NULL) &&
               ((ty_i->kind == NOLL_TYP_INT) ||
                (ty_i->kind == NOLL_TYP_BAGINT)))
        {                       /// it is a data argument, mark it as explored
          vg[noll_vector_at (args, i)] = 2;
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
   * Mark the edges outgoing from vg (except from target and border) as used.
   * Insert the edges labeled by labels in L2 in the result.
   */
  for (uint_t v = 0; v < vg_size; v++)
    {
      if (vg[v] == 0 || vg[v] == 2 ||
          (vg[v] == 1 && (noll_pred_is_one_dir (label) == false)))
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
                  if (eg[ei] == 1)
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
          if ((i == 0 || vg[i] >= 0) && (j == 0 || vg[j] >= 0))
            rg->diff[i][j] = g->diff[i][j];
        }
    }
  goto return_select_ls;

return_select_ls_error:
  /* redo the used edges */
  for (uint_t v = 0; v < vg_size; v++)
    {
      if (vg[v] == 0 || vg[v] == 2 ||
          (vg[v] == 1 && (noll_pred_is_one_dir (label) == false)))
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
 * Check well-formedness condition 0 
 * for the graph selected @param sg2 wrt @param g2, i.e.,
 * if sg2 contains a pto, 
 * then g2 ==> args2[0] != args2[1+isdll] [+ dll]
 * 
 * @param g2    the selection
 * @param sg2   the selection
 * @param args2 the arguments (nodes) of e1 maped with the homeomorphism
 * @param isdll 1 if is a dll pred
 * @return      1 if well-formed, 0 otherwise
 */
int
noll_shom_select_wf_0 (noll_graph_t * g2, noll_graph_t * sg2,
                       noll_uid_array * args2, int isdll)
{
  assert (NULL != sg2);
  assert (NULL != g2);
  assert (NULL != args2);

  int res = 1;
  /* search for a pto edge in sg2 */
  bool found = false;
  for (uint_t eid2 = 0;
       eid2 < noll_vector_size (sg2->edges) && !found; eid2++)
    {
      noll_edge_t *e2 = noll_vector_at (sg2->edges, eid2);
      if (e2->kind == NOLL_EDGE_PTO)
        {
          found = true;
        }
    }
  if (found == false)
    return res;                 /* 1 */

  /* if found, then check that the non-empty case of the predicate
   * is satisfied, i.e.,
   * - for one direction lists : g2 ==> args2[0] != args2[>=1]
   * - for dll lists : g2 ==> (args2[0] != args2[>=1+isdll] && args[1] != args[2])
   */
  /* go through the arguments in args2
   * to check the boolean constraint */
  uid_t fst = noll_vector_at (args2, 0);
  for (uint_t i = 1 + isdll; i < noll_vector_size (args2) && (res == 1); i++)
    {
      uid_t nv = noll_vector_at (args2, i);
      // check the query Bool(g2) => ![fst=nv], i.e.,
      uid_t ni = (nv > fst) ? nv : fst;
      uid_t nj = (nv > fst) ? fst : nv;
      res = (g2->diff[ni][nj]) ? 1 : 0;
#ifndef NDEBUG
      NOLL_DEBUG ("\n++++ select_wf_0 for [n%d != n%d] returns %d\n", nv,
                  fst, res);
#endif
      if (res != 1)
        {
          if (noll_option_is_diag () == true)
            {
              fprintf (stdout, "\nDiagnosis of failure: ");
              fprintf (stdout, "\n\tMissing constraint: %s != %s\n",
                       noll_var_name (g2->lvars,
                                      noll_graph_get_var (g2, fst),
                                      NOLL_TYP_RECORD),
                       noll_var_name (g2->lvars, noll_graph_get_var (g2, nv),
                                      NOLL_TYP_RECORD));
              fprintf (stdout, "\t(required by well formedness).\n");
            }
          return 0;
        }
    }
  if (isdll >= 1)
    {
      uid_t bk = noll_vector_at (args2, 1);
      uid_t pr = noll_vector_at (args2, 2);
      uid_t ni = (bk > pr) ? bk : pr;
      uid_t nj = (bk > pr) ? pr : bk;
      res = (g2->diff[ni][nj]) ? 1 : 0;
#ifndef NDEBUG
      NOLL_DEBUG ("\n++++ select_wf_0 for [n%d != n%d] returns %d\n", bk,
                  pr, res);
#endif
      if (res != 1)
        {
          if (noll_option_is_diag () == true)
            {
              fprintf (stdout, "\nDiagnosis of failure: ");
              fprintf (stdout, "\n\tMissing constraint: %s != %s\n",
                       noll_var_name (g2->lvars,
                                      noll_graph_get_var (g2, bk),
                                      NOLL_TYP_RECORD),
                       noll_var_name (g2->lvars, noll_graph_get_var (g2, pr),
                                      NOLL_TYP_RECORD));
              fprintf (stdout, "\t(required by well formedness).\n");
            }
          return 0;
        }
    }
  return 1;
}

/**
 * Check well-formedness condition 1 
 * for the graph selected @p sg2 wrt @p g2, i.e.,
 * for any predicate edge P(E,F,...) in sg2, 
 *   check that (g2 \ sg2) /\ E != F ==> args2[1] allocated or nil 
 *          (for dll check args2[2] and args[3] allocated or nil)
 * @param g2    the origin of the selection
 * @param sg2   the selected graph
 * @param args2 the arguments (nodes) of e1 maped with the homeomorphism
 * @param isdll 1 if is a dll pred
 * @return      1 if well-formed, 0 otherwise
 */
int
noll_shom_select_wf_1 (noll_graph_t * g2, noll_graph_t * sg2,
                       noll_uid_array * args2, int isdll)
{
  assert (NULL != sg2);
  assert (NULL != g2);
  assert (NULL != args2);

  /* case args2[1+isdll] is nil */
  if ((isdll == 0) && (noll_vector_at (args2, 1) == g2->var2node[0]))
    {
#ifndef NDEBUG
      NOLL_DEBUG ("\n++++ select_wf_1: not dll and nxt is nil\n");
#endif
      return 1;
    }
  /// case args[1+isdll] is not a location variable
  uint_t nF = noll_vector_at (args2, 1 + isdll);
  uint_t vF = noll_graph_get_var (g2, nF);
  noll_type_t *ty_F = noll_var_type (sg2->lvars, vF);
#ifndef NDEBUG
  fprintf (stdout, "\n++++ select_wf_1: arg-%d of type %d\n",
           1 + isdll, ty_F->kind);
#endif
  if (ty_F->kind != NOLL_TYP_RECORD)
    {
#ifndef NDEBUG
      NOLL_DEBUG ("\n++++ select_wf_1: not a location arg\n");
#endif
      return 1;
    }

  if ((isdll >= 1) &&
      (noll_vector_at (args2, 2) == g2->var2node[0]) &&
      (noll_vector_at (args2, 3) == g2->var2node[0]))
    {
#ifndef NDEBUG
      NOLL_DEBUG ("\n++++ select_wf_1: dll and nxt+prv are nil\n");
#endif
      return 1;
    }
  /* check condition for any e2 in sg2 such that e2(dst) != args2[1+isdll] */
  for (uint_t eid2 = 0; eid2 < noll_vector_size (sg2->edges); eid2++)
    {
      noll_edge_t *e2 = noll_vector_at (sg2->edges, eid2);
      if (e2->kind != NOLL_EDGE_PRED)
        continue;
      /// only if e2->args[1+isdll] is a location argument then do the check
      uint_t nF = noll_vector_at (e2->args, 1 + isdll);
      uint_t vF = noll_graph_get_var (sg2, nF);
      noll_type_t *ty_F = noll_var_type (sg2->lvars, vF);
#ifndef NDEBUG
      fprintf (stdout, "\n++++ select_wf_1: arg-%d of type %d\n",
               1 + isdll, ty_F->kind);
#endif
      if (ty_F->kind != NOLL_TYP_RECORD)
        continue;
      if (noll_vector_at (e2->args, 1 + isdll) ==
          noll_vector_at (args2, 1 + isdll))
        {
          /* ignore edges of sg2 with the same destination node */
          continue;
        }
      else if (NOLL_VECTOR_SIZE (g2->edges) == NOLL_VECTOR_SIZE (sg2->edges))
        {
#ifndef NDEBUG
          NOLL_DEBUG ("\n++++ select_wf_1: empty g2 \\ sg2!\n");
#endif
          /* weaker condition: */
          /* not the same target, and empty remaining graph */
          return 0;
        }
    }
#ifndef NDEBUG
  NOLL_DEBUG ("\n++++ select_wf_1: NYI!\n");
#endif
  return 1;
}

/**
 * Check well-formedness condition 2
 * for the graph selected, i.e., @param sg2 wrt @param g2, i.e.,
 * for any pto in sg2 from some V' 
 *   check that g2 ==> V' != V
 * 
 * @param g2    the selection
 * @param sg2   the selection
 * @param args2 the arguments (nodes) of e1 maped with the homeomorphism
 * @param isdll 1 if is a dll pred
 * @return      1 if well-formed, 0 otherwise
 */
int
noll_shom_select_wf_2 (noll_graph_t * g2, noll_graph_t * sg2,
                       noll_uid_array * args2, int isdll)
{
  assert (NULL != sg2);
  assert (NULL != g2);
  assert (NULL != args2);

  int res = 1;
  /* condition 2:
   * for any V in args2[1+isdll,...] do
   *   for any e'=V'--> ... in sg2 do
   *     check unsat Bool(g1) => ![V=V']
   */
  /* collect all V' origin of some pto in sg2 */
  noll_uid_array *src_pto = noll_uid_array_new ();
  for (uint_t eid2 = 0; eid2 < noll_vector_size (sg2->edges); eid2++)
    {
      noll_edge_t *e2 = noll_vector_at (sg2->edges, eid2);
      if (e2->kind == NOLL_EDGE_PTO)
        {
          uid_t src = noll_vector_at (e2->args, 0);
          noll_uid_array_push (src_pto, src);
        }
    }
  if (noll_vector_empty (src_pto))
    {
      // no check needed
      noll_uid_array_delete (src_pto);
      return res;               // 1
    }

  /* go through the arguments in args2
   * to check the boolean constraint */
  for (uint_t i = 1 + isdll; i < noll_vector_size (args2) && (res == 1); i++)
    {
      uid_t nv = noll_vector_at (args2, i);
      for (uint_t j = 0; j < noll_vector_size (src_pto) && (res == 1); j++)
        {
          uid_t nvp = noll_vector_at (src_pto, j);
          // check the query Bool(g1) => ![V=V'], i.e.,
          // there is a difference edge between V and V'
          // in the low diagonal matrix og g2->diff
          uid_t ni = (nv > nvp) ? nv : nvp;
          uid_t nj = (nv > nvp) ? nvp : nv;
          res = (g2->diff[ni][nj]) ? 1 : 0;
#ifndef NDEBUG
          NOLL_DEBUG ("\n++++ select_wf_2 for [%d != %d] returns %d\n", nv,
                      nvp, res);
#endif
          if (res == 0)
            {
              if (noll_option_is_diag () == true)
                {
                  fprintf (stdout, "\nDiagnosis of failure:");
                  fprintf (stdout, "\n\tMissing constraint: %s != %s\n",
                           noll_var_name (g2->lvars,
                                          noll_graph_get_var (g2, ni),
                                          NOLL_TYP_RECORD),
                           noll_var_name (g2->lvars,
                                          noll_graph_get_var (g2, nj),
                                          NOLL_TYP_RECORD));
                  fprintf (stdout, "\t(required by well formedness).\n");
                }
              // loop is broken
            }
        }
    }
  noll_uid_array_delete (src_pto);
  return res;
}

/**
 * Check well-formedness for the graphs selected &param sg2 wrt g2.
 * @param g2    the selection
 * @param sg2   the selection
 * @param args2 the arguments (nodes) of e1 maped with the homeomorphism
 * @param isdll 1 if is a dll pred
 * @return      1 if well-formed, 0 otherwise
 */
int
noll_shom_select_wf (noll_graph_t * g2, noll_graph_t * sg2,
                     noll_uid_array * args2, int isdll)
{
  assert (NULL != sg2);
  assert (NULL != g2);
  assert (NULL != args2);

  /* check wf condition 0: 
   * if sg2 contains a pto, 
   * then g2 ==> args2[0] != args2[1+isdll] */
  int res = noll_shom_select_wf_0 (g2, sg2, args2, isdll);
  if (res == 0)
    return res;
  /* check wf condition 1:
   * for any predicate edge P(E,F,...) in sg2, 
   *   check that (g2 \ sg2) /\ E != F ==> args2[1+isdll] allocated or nil 
   */
  res = noll_shom_select_wf_1 (g2, sg2, args2, isdll);
  if (res == 0)
    return res;
  /* check wf condition 2: 
   * for any pto in sg2 from some V' 
   *   check that g2 ==> V' != V
   */
  res = noll_shom_select_wf_2 (g2, sg2, args2, isdll);
  return res;
}

int
noll_shom_check_TA (noll_graph_t * g2, noll_edge_t * e1, noll_uid_array * h);
int noll_shom_check_syn (noll_graph_t * g2, noll_edge_t * e1,
                         noll_uid_array * args2);

/**
 * Check that the graph in @p g2 is an unfolding of the edge @p e1.
 * The mapping of the arguments of @p e1 on nodes of @p g2 are given by @p h.
 */
int
noll_shom_check (noll_graph_t * g2, noll_edge_t * e1, noll_uid_array * h)
{

  /* pre-conditions */
  assert (g2 != NULL);
  assert (e1 != NULL);
  assert (h != NULL);

  /* TODO: select the method of checking entailment using the option */
  if (noll_option_is_checkTA () == true)
    return noll_shom_check_TA (g2, e1, h);
  else
    return noll_shom_check_syn (g2, e1, h);

}

/**
 * Apply the procedure based on Tree Automata for fragment of
 * simple recursive definitions.
 */
int
noll_shom_check_TA (noll_graph_t * g2, noll_edge_t * e1, noll_uid_array * h)
{
  if (noll_pred_is_one_dir (e1->label) == false)
    {
      // special case for generating TA from graphs with dll
      noll_graph_dll (g2, e1->label);
    }
  noll_tree_t *g2_tree = noll_graph2ta (g2, h);
  if (NULL == g2_tree)
    {                           // if the graph could not be translated to a tree
      NOLL_DEBUG ("Could not translate the graph into a tree!\n");
      return 0;
    }

  noll_ta_t *g2_ta = noll_tree_to_ta (g2_tree);
  assert (NULL != g2_ta);
  noll_tree_free (g2_tree);
#ifndef NDEBUG
  NOLL_DEBUG ("\nGraph TA:\n");
  vata_print_ta (g2_ta);
  NOLL_DEBUG ("\n");
#endif

  noll_ta_t *e1_ta = noll_edge2ta (e1);
  if (NULL == e1_ta)
    {                           // if the edge could not be translated to a tree automaton
      NOLL_DEBUG ("Could not translate the edge into a tree automaton!\n");
      return 0;
    }

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
 * @brief Check that @p g2 implies the pure part of @p rule updated with @p m.
 * 
 * @param g2     the graph 
 * @param rule   the base rule (i.e., only pure is filled)
 * @param m      the mapping of vars in @p rule to nodes in @p g2
 * @return       1 when the constraints are satisfied, 0 otherwise
 */
int
noll_shom_match_form_pure (noll_graph_t * g2,
                           noll_pure_t * fpure, noll_uid_map * m)
{
  assert (g2 != NULL);
  assert (fpure != NULL);
  assert (m != NULL);

  /// more checks: the pure part is not empty
  assert (fpure->m != NULL);

#ifndef NDEBUG
  NOLL_DEBUG ("\nshom_match_pure: pure size=%d, map size = %d\n",
              fpure->size, noll_vector_size (m));
#endif
  //assert (fpure->size == noll_vector_size (m));

  /// call procedure for equality and disequalities over locations
  /// may update m for non-location vars
  int res = noll_pure_check_entl (g2->diff, g2->nodes_size,
                                  fpure, m);
  if (res == 0)
    return res;

#ifndef NDEBUG
  NOLL_DEBUG ("\nshom_match_pure: pure part check succeeded\n");
#endif

  res = noll_dform_check_entl (g2->lvars, g2->var2node,
                               g2->diff, g2->nodes_size, g2->data, fpure, m);
  return res;
}

/**
 * Match the formula @p fpto with edges in @p g2 using the mapping
 * of vars ids @p sigma.
 * 
 * @param g2     the graph 
 * @param fpto   the formula
 * @param sigma  the mapping of vars in @p fpto to nodes in @p g2
 * @param eid1   the edge unfolded here 
 * @return       the edges of @p g2 matched or NULL
 */
noll_uid_array *
noll_shom_match_form_pto (noll_graph_t * g2, noll_space_t * fpto,
                          noll_uid_array * sigma, uid_t eid1)
{
  assert (g2 != NULL);
  assert (fpto != NULL);
  assert (fpto->kind == NOLL_SPACE_PTO);
  assert (sigma != NULL);

  // prepare the result
  noll_uid_array *res = noll_uid_array_new ();
  noll_uid_array_reserve (res, noll_vector_size (g2->edges));
  for (uid_t ei = 0; ei < noll_vector_size (g2->edges); ei++)
    {
      noll_uid_array_push (res, UNDEFINED_ID);
    }
  // make a copy of sigma in case of failure
  noll_uid_array *sigmap = noll_uid_array_new ();
  noll_uid_array_copy (sigmap, sigma);

  // compute the source node of all edges
  assert (fpto->m.pto.sid < noll_vector_size (sigma));
  uint_t nsrc = noll_vector_at (sigma, fpto->m.pto.sid);
#ifndef NDEBUG
  NOLL_DEBUG ("\nStarting matching pto from n%d (v%d < %d)\n",
              nsrc, fpto->m.pto.sid, noll_vector_size (sigma));
#endif
  noll_uid_array *edges_nsrc = g2->mat[nsrc];
  if (edges_nsrc == NULL)
    {
#ifndef NDEBUG
      NOLL_DEBUG ("\nMatching pto fails : no edge from n%d\n", nsrc);
#endif
      noll_uid_array_delete (sigmap);
      noll_uid_array_delete (res);
      return NULL;
    }
  // TODO: improve the complexity!
  for (uint fi = 0; fi < noll_vector_size (fpto->m.pto.fields); fi++)
    {
      uid_t fid = noll_vector_at (fpto->m.pto.fields, fi);
      // search the edge from nsrc with label fid
      bool found = false;
      for (uint i2 = 0;
           i2 < noll_vector_size (edges_nsrc) && (found == false); i2++)
        {
          uid_t eid2 = noll_vector_at (edges_nsrc, i2);
          noll_edge_t *ei2 = noll_vector_at (g2->edges, eid2);
          if (ei2->kind == NOLL_EDGE_PTO && ei2->label == fid)
            {
              found = true;
              noll_uid_array_set (res, eid2, eid1);
              uint_t dst = noll_vector_at (fpto->m.pto.dest, fi);
              uint_t ndst = noll_vector_at (ei2->args, 1);
              noll_uid_array_set (sigmap, dst, ndst);
#ifndef NDEBUG
              NOLL_DEBUG
                ("\nUnfolding e(1)%d: match pto edge e(2)%d: n%d(v%d) --f%d--> n%d(v%d) nsrc=%d\n",
                 eid1, eid2, noll_vector_at (ei2->args, 0), fpto->m.pto.sid,
                 fid, noll_vector_at (ei2->args, 1), dst, nsrc);
              // getchar();
#endif
            }
        }
      if (found == false)
        {
#ifndef NDEBUG
          NOLL_DEBUG ("\nMatching pto fails for field %d\n", fid);
#endif
          noll_uid_array_delete (sigmap);
          noll_uid_array_delete (res);
          return NULL;
        }
    }
  // matching succeeded, update sigma and return res
  for (uint i = 0; i < noll_vector_size (sigmap); i++)
    if (noll_vector_at (sigma, i) == UNDEFINED_ID)
      noll_vector_at (sigma, i) = noll_vector_at (sigmap, i);

  noll_uid_array_delete (sigmap);
#ifndef NDEBUG
  NOLL_DEBUG ("\nMatching pto result: [");
  for (uint i = 0; i < noll_vector_size (res); i++)
    NOLL_DEBUG ("%d,", noll_vector_at (res, i));
  NOLL_DEBUG ("]\n");
#endif
  return res;
}

noll_uid_array *noll_shom_match_rd (noll_graph_t * g2, uid_t pid,
                                    noll_uid_array * args2, uid_t eid1);

/**
 * Match the formula @p fpred with edges in @p g2 using the mapping
 * of vars ids @p sigma. It mainly prepares the aguments for 
 * @see noll_shom_match_rd.
 * 
 * @param g2     the graph 
 * @param fpto   the predicate atom 
 * @param map    the mapping of vars in @p fpred to nodes in @p g2
 * @param eid1   the edge unfolded here 
 * @return       the edges of @p g2 matched or NULL
 */
noll_uid_array *
noll_shom_match_form_rd (noll_graph_t * g2, noll_space_t * fpred,
                         noll_uid_array * map, uid_t eid1)
{
  assert (g2 != NULL);
  assert (fpred != NULL);
  assert (fpred->kind == NOLL_SPACE_LS);
  assert (map != NULL);

  // get the label of the predicate
  uint_t pid = fpred->m.ls.pid;

  // get the arguments of the predicate
  noll_uid_array *args = fpred->m.ls.args;
  // prepare the args2
  noll_uid_array *args2 =       // TODO: check that the semantics corresponds
    noll_uid_map_apply (map, args,
                        noll_pred_use_nil (pid));
  // call match_rd
  noll_uid_array *res = noll_shom_match_rd (g2, pid, args2, eid1);
  // if success, update sigma
  if (res != NULL)
    {
      uint_t sz = noll_vector_size (args);
      if (noll_pred_use_nil (pid))
        sz--;                   /// do not check nil 
      for (uint_t i = 0; i < sz; i++)
        {
          uid_t vi = noll_vector_at (args, i);
          uid_t ni = noll_vector_at (args2, i);
          if ((noll_vector_at (map, vi) == UNDEFINED_ID) &&
              (ni != UNDEFINED_ID))
            {
              /// mapping updated by matching
              noll_uid_array_set (map, vi, ni);
            }
        }
    }
  noll_uid_map_delete (args2);
  return res;
}

/**
 * Compose two mappings of the same length.
 * The mappings shall agree on defined values.
 * 
 * @param dst  the mapping where composition is done
 * @param src  the mapping used to update
 * @return     the @p dst if composition is correct, NULL otherwise
 */
noll_uid_array *
noll_uid_array_compose (noll_uid_array * dst, noll_uid_array * src)
{
  assert (dst != NULL);
  assert (src != NULL);
  assert (noll_vector_size (dst) == noll_vector_size (src));

  // check that mappings agree on defined values
  for (uint i = 0; i < noll_vector_size (dst); i++)
    if ((noll_vector_at (dst, i) != UNDEFINED_ID) &&
        (noll_vector_at (src, i) != UNDEFINED_ID) &&
        (noll_vector_at (dst, i) != noll_vector_at (src, i)))
      return NULL;
  // composition can be done
  for (uint i = 0; i < noll_vector_size (dst); i++)
    if ((noll_vector_at (dst, i) == UNDEFINED_ID) &&
        (noll_vector_at (src, i) != UNDEFINED_ID))
      noll_vector_at (dst, i) = noll_vector_at (src, i);
  return dst;
}

/**
 * @brief Try to match the base rule @p rule.
 */
int
noll_shom_match_rule_base (noll_graph_t * g2, noll_pred_rule_t * rule,
                           noll_uid_array * args2)
{
  assert (rule != NULL);

/// check that it is indeed a basic rule
  assert (rule->nst == NULL);   // TODO: or empty?
  assert (rule->rec == NULL);
  noll_uid_array *lmap = noll_uid_array_new ();
  noll_uid_array_reserve (lmap, noll_vector_size (rule->vars));
  noll_uid_array_push (lmap, g2->var2node[0]);  /// push nil
  for (uint i = 0; i < rule->fargs; i++)
    /// push formal args given by args2
    noll_uid_array_push (lmap, noll_vector_at (args2, i));
  int res = noll_shom_match_form_pure (g2, rule->pure, lmap);
  noll_uid_array_delete (lmap);
  return res;
}

/**
 * @brief Try to match the recursive rule @p rule.
 * 
 * @return the mapping of edges in @p g2 matching eid1, NULL otherwise
 */
noll_uid_array *
noll_shom_match_rule_rec (noll_graph_t * g2, uid_t pid,
                          noll_pred_rule_t * rule, noll_uid_array * args2,
                          uid_t eid1)
{
  assert (rule != NULL);

  /// check that it is indeed a recursive rule
  assert (rule->pto != NULL);
  assert (rule->rec != NULL);

  /// rule = exists X. pure /\ pto * nst * rec
  const noll_pred_t *e1_pred = noll_pred_getpred (pid);
  /// match first pto because pure may contain constraints on X
  noll_space_t *e1_pto = rule->pto;
  assert (e1_pto != NULL);
  assert (e1_pto->kind == NOLL_SPACE_PTO);

  /// build mapping of X to nodes of @p g2 using e1_pto
  // Warning: in the examples considered, this mapping maps all X
  // TODO: change to consider partial mappings of X + 
  //       combinatorial choice for other vars
  noll_uid_array *lmap = noll_uid_array_new ();
  noll_uid_array_reserve (lmap, noll_vector_size (rule->vars));
  noll_uid_array_push (lmap, g2->var2node[0]);  /// push nil
  for (uint i = 0; i < rule->fargs; i++)
    /// push formal args given by args2
    noll_uid_array_push (lmap, noll_vector_at (args2, i));
  /// push undefined node for local vars
  for (uint i = rule->fargs + 1; i < noll_vector_size (rule->vars); i++)
    /// push undefined values for X
    noll_uid_array_push (lmap, UNDEFINED_ID);

  /// updates lmap
  noll_uid_array *res = noll_shom_match_form_pto (g2, e1_pto, lmap, eid1);
  if (NULL == res)
    {                           /// unsuccessfull matching 
#ifndef NDEBUG
      NOLL_DEBUG ("\nSyntactic matching recursive rule: pto fails!\n");
#endif
      // TODO: search another rule
      // Warning: works for only one rule
      noll_uid_array_delete (lmap);
      return NULL;
    }
#ifndef NDEBUG
  NOLL_DEBUG
    ("\nSyntactic matching recursive rule: pto succeeds!\nres found: ");
  noll_uid_map_fprint (stdout, res);
  NOLL_DEBUG ("\nlmap: ");
  noll_uid_map_fprint (stdout, lmap);
#endif

  /// successfull matching, continue with the nested and recursive part
  for (uint_t i = 0; i < 2; i++)
    {
      noll_space_t *e1_space = (i == 0) ? rule->nst : rule->rec;
      // Warning: it works for lmap a fully defined for location vars
      // TODO: extend when lmap is partially defined
      noll_uid_array *resr = NULL;
      if (e1_space != NULL)
        {
          if (e1_space->kind == NOLL_SPACE_LS)
            {
              resr = noll_shom_match_form_rd (g2, e1_space, lmap, eid1);
              if (resr == NULL)
                {
#ifndef NDEBUG
                  NOLL_DEBUG
                    ("\nSyntactic matching recursive rule: rec call %d fails!\n",
                     eid1);
#endif
                  noll_uid_array_delete (lmap);
                  noll_uid_array_delete (res);
                  return NULL;
                }
              if (noll_uid_array_compose (res, resr) == NULL)
                {
#ifndef NDEBUG
                  NOLL_DEBUG
                    ("\nSyntactic matching recursive rule: rec call %d use same edges!\n",
                     eid1);
#endif
                  noll_uid_array_delete (lmap);
                  noll_uid_array_delete (res);
                  noll_uid_array_delete (resr);
                  return NULL;
                }
#ifndef NDEBUG
              NOLL_DEBUG
                ("\nSyntactic matching recursive rule: eid-%d succeeds!\nmap computed ",
                 eid1);
              noll_uid_map_fprint (stdout, res);
#endif
              noll_uid_array_delete (resr);
            }
          else
            {
              /// a list of recursive calls
              assert (e1_space->kind == NOLL_SPACE_SSEP);
              for (uint i = 0; i < noll_vector_size (e1_space->m.sep); i++)
                {
                  noll_space_t *si = noll_vector_at (e1_space->m.sep, i);
                  assert (si->kind == NOLL_SPACE_LS);
                  resr = noll_shom_match_form_rd (g2, si, lmap, eid1);
                  if (resr == NULL)
                    {
#ifndef NDEBUG
                      NOLL_DEBUG
                        ("\nSyntactic matching recursive rule: rec call %d fails!\n",
                         i);
#endif
                      noll_uid_array_delete (lmap);
                      noll_uid_array_delete (res);
                      return NULL;
                    }
                  if (noll_uid_array_compose (res, resr) == NULL)
                    {
#ifndef NDEBUG
                      NOLL_DEBUG
                        ("\nSyntactic matching recursive rule: rec call %d use same edges!\n",
                         i);
#endif
                      noll_uid_array_delete (lmap);
                      noll_uid_array_delete (res);
                      noll_uid_array_delete (resr);
                      return NULL;
                    }
#ifndef NDEBUG
                  NOLL_DEBUG
                    ("\nSyntactic matching recursive rule: rec call %d succeeds!\n",
                     i);
                  noll_uid_map_fprint (stdout, res);
#endif
                  noll_uid_array_delete (resr);
                }
            }
        }
    }

  /// check the pure part
  int pure_ok = noll_shom_match_form_pure (g2, rule->pure, lmap);
  if (pure_ok == 0)
    {
#ifndef NDEBUG
      NOLL_DEBUG ("\nSyntactic matching recursive rule: pure fails!\n");
#endif
      noll_uid_array_delete (lmap);
      noll_uid_array_delete (res);
      return NULL;
    }

  if (lmap != NULL)
    noll_uid_array_delete (lmap);
  return res;
}

noll_uid_map *
noll_shom_match_lemma (noll_graph_t * g2, uid_t pid, noll_lemma_t * lemma,
                       noll_uid_array * args2, uid_t eid1)
{
  assert (lemma != NULL);
  assert (lemma->pid == pid);
#ifndef NDEBUG
  NOLL_DEBUG ("\nshom_match_lemma: start with lemma\n");
  noll_lemma_fprint (stdout, lemma);
#endif

  /// get the edge starting from args2[0]
  noll_uid_array *nE_edges = g2->mat[noll_vector_at (args2, 0)];
  if ((nE_edges == NULL) || (noll_vector_size (nE_edges) > 1))
    {
#ifndef NDEBUG
      NOLL_DEBUG
        ("\nshom_match_lemma: NYI case of 0 or more than one edge from n%d",
         noll_vector_at (args2, 0));
#endif
      return NULL;
    }
  assert (noll_vector_size (nE_edges) == 1);
  /// that is a predicate edge = or <> from pid!
  uid_t eidE = noll_vector_at (nE_edges, 0);
  noll_edge_t *edgeE = noll_vector_at (g2->edges, eidE);
  if (edgeE == NULL || edgeE->kind != NOLL_EDGE_PRED)
    {
#ifndef NDEBUG
      NOLL_DEBUG
        ("\nshom_match_lemma: NYI case of 0 or not predicate edge n%d",
         noll_vector_at (args2, 0));
#endif
      return NULL;
    }
  /// ok, lemma matching can be done
  /// create mapping of local vars
  noll_uid_array *lmap = noll_uid_array_new ();
  noll_uid_array_reserve (lmap, noll_vector_size (lemma->rule.vars));
  noll_uid_array_push (lmap, g2->var2node[0]);  /// push nil
  for (uint i = 0; i < lemma->rule.fargs; i++)
    /// push formal args given by args2
    noll_uid_array_push (lmap, noll_vector_at (args2, i));
  /// push undefined node for local vars
  for (uint i = lemma->rule.fargs + 1;
       i < noll_vector_size (lemma->rule.vars); i++)
    /// push undefined values for X
    noll_uid_array_push (lmap, UNDEFINED_ID);

  /// prepare the result
  int isErr = 0;
  noll_uid_map *res = noll_uid_map_new (noll_vector_size (g2->edges));

  /// match the edgeE with the "first" predicate edge in lemma
  noll_space_t *predE = noll_lemma_getspace (lemma, 0);
  if (predE == NULL || predE->kind != NOLL_SPACE_LS)
    {
#ifndef NDEBUG
      NOLL_DEBUG ("\nshom_match_lemma: no pred in lemma!\n");
#endif
      isErr = 1;
      goto shom_match_lemma;
    }
  if ((predE->m.ls.pid != edgeE->label) ||
      (noll_vector_size (predE->m.ls.args) != noll_vector_size (edgeE->args)))
    {
#ifndef NDEBUG
      NOLL_DEBUG
        ("\nshom_match_lemma:  bad edge for the first pred in lemma!\n");
#endif
      isErr = 1;
      goto shom_match_lemma;
    }
  /// match arguments of predE with arguments of edgeE and update lmap
  for (uint_t i = 0; i < noll_vector_size (predE->m.ls.args); i++)
    {
      uid_t vi = noll_vector_at (predE->m.ls.args, i);
      assert (vi < noll_vector_size (lmap));
      uid_t ni = noll_vector_at (edgeE->args, i);
      uid_t lni = noll_vector_at (lmap, vi);
      if (lni == UNDEFINED_ID)
        noll_uid_array_set (lmap, vi, ni);
      else if (ni != lni)
        {
#ifndef NDEBUG
          NOLL_DEBUG
            ("\nshom_match_lemma:  bad matching for first pred in lemma!\n");
#endif
          isErr = 1;
          goto shom_match_lemma;
        }
      /// else, continue
    }
#ifndef NDEBUG
  NOLL_DEBUG ("\nshom_match_lemma: vars mapping found:\n");
  noll_uid_map_fprint (stdout, lmap);
#endif
  /// edge matched, set res
  noll_uid_array_set (res, eidE, eid1);
  /// now, all the local variables shall be matched to nodes

  /// check pure part, if any
  if (lemma->rule.pure != NULL)
    {
      int r = noll_shom_match_form_pure (g2, lemma->rule.pure, lmap);
      if (r == 0)
        {
#ifndef NDEBUG
          NOLL_DEBUG
            ("\nshom_match_lemma: bad matching of pure constraint in lemma!\n");
#endif
          isErr = 1;
          goto shom_match_lemma;
        }
    }

  /// check remainder part, if any
  predE = noll_lemma_getspace (lemma, 1);
  if (predE == NULL)
    goto shom_match_lemma;
  if (predE->kind != NOLL_SPACE_LS)
    {
#ifndef NDEBUG
      NOLL_DEBUG ("\nshom_match_lemma: bad second part in lemma!\n");
#endif
      isErr = 1;
      goto shom_match_lemma;
    }
  noll_uid_array *resr = noll_shom_match_form_rd (g2, predE, lmap, eid1);
  /// check that the resr is not using eidE
  if (resr == NULL)
    {
#ifndef NDEBUG
      NOLL_DEBUG
        ("\nshom_match_lemma: no matching for second part in lemma!\n");
#endif
      isErr = 1;
      goto shom_match_lemma;
    }
  if (noll_vector_at (resr, eidE) != UNDEFINED_ID)
    {
#ifndef NDEBUG
      NOLL_DEBUG
        ("\nshom_match_lemma: matching of second part uses un already used edge!\n");
#endif
      isErr = 1;
      goto shom_match_lemma;
    }
  /// compose results
  noll_uid_array_compose (res, resr);
  noll_uid_array_delete (resr);

shom_match_lemma:
  if (isErr == 1)
    {
      if (res != NULL)
        noll_uid_map_delete (res);
      res = NULL;
    }
  noll_uid_array_delete (lmap);

  return res;
}

/**
 * @brief Check that the graph @p g2 **includes** an unfolding of the 
 * predicate @p pid.
 * 
 * The predicate @p pid has as arguments the list of nodes by @p args2.
 * If the matching holds, the procedure computes a set of edges of
 * @p g2 used, in the form of an array of size @p g2->edges,
 * mapping each edge to UNDEFINED_ID or the @p eid1, the identifier 
 * of the original edge in right hand side of the entailment.
 * 
 * @param g2     the full graph for searching the predicate unfolding
 * @param pid    the edge to be matched labeled by predicate @p e1->label
 * @param args2  [inout] the maping of variables used in @p e1 to nodes of @p g2 
 * @param eid1   the identifier of the unfolded edge 
 * @return       the set of edges used by the predicate unfolding,
 *               NULL if the matching does not hold
 */
noll_uid_array *
noll_shom_match_rd (noll_graph_t * g2, uid_t pid, noll_uid_array * args2,
                    uid_t eid1)
{
  assert (g2 != NULL);
  assert (pid < noll_vector_size (preds_array));
  assert (args2 != NULL);

  /// prepare the result = mapping of g2 edges to g1 edges or UNDEFINED_ID
  noll_uid_map *res = noll_uid_map_new (noll_vector_size (g2->edges));

  /** 
   * Step 1: search the edge labeled by @p pid in g2
   *         at g2->mat[args2[0]] (or 1 if nil)
   */
#ifndef NDEBUG
  NOLL_DEBUG ("\nSyntactic matching: exact edge starts\n");
#endif
  uint_t eid2 = noll_graph_get_edge (g2, NOLL_EDGE_PRED, pid, args2);
  if (eid2 != UNDEFINED_ID)
    {
      noll_uid_map_set (res, eid2, eid1);
#ifndef NDEBUG
      NOLL_DEBUG ("\nSyntactic matching 1 predicate edge!\nmap found: ");
      noll_uid_map_fprint (stderr, res);
#endif
      return res;
    }
  // else, try the rules and the lemma of the predicate @p pid

  const noll_pred_t *pred = noll_pred_getpred (pid);

  /**
   * Step 2: check the base rules of P. 
   * No matching is generated.
   */
#ifndef NDEBUG
  NOLL_DEBUG ("\nSyntactic matching: unfolding base rules starts\n");
#endif
  assert (pred->def->base_rules != NULL);
  int found = 0;
  for (uint_t ri = 0; (ri < noll_vector_size (pred->def->base_rules)) &&
       (found == 0); ri++)
    {
      noll_pred_rule_t *rule_i = noll_vector_at (pred->def->base_rules, ri);
      found = noll_shom_match_rule_base (g2, rule_i, args2);
    }
  if (found)
    {
#ifndef NDEBUG
      NOLL_DEBUG ("\nSyntactic matching base case of pred-%d!\nmap found: ",
                  pid);
      noll_uid_map_fprint (stderr, res);
#endif
      return res;
    }

  /// in the following, res will be computed
  noll_uid_array_delete (res);
  res = NULL;

  /**
   * Step 3: test the recursive rules of P.
   * The matching res is computed.
   */
#ifndef NDEBUG
  NOLL_DEBUG ("\nSyntactic matching: unfolding recursive rules starts\n");
#endif
  assert (pred->def->rec_rules != NULL);
  for (uint_t ri = 0; (ri < noll_vector_size (pred->def->rec_rules)) &&
       (res == NULL); ri++)
    {
      noll_pred_rule_t *rule_i = noll_vector_at (pred->def->rec_rules, ri);
      res = noll_shom_match_rule_rec (g2, pid, rule_i, args2, eid1);
    }
  if (res != NULL)
    {
#ifndef NDEBUG
      NOLL_DEBUG ("\nSyntactic matching rec case of pred-%d!\nmap found: ",
                  pid);
      noll_uid_map_fprint (stderr, res);
#endif
      return res;
    }

  /**
   * Step 4: test the lemma of P.
   * The matching res is computed.
   */
#ifndef NDEBUG
  NOLL_DEBUG ("\nSyntactic matching: applying lemma starts\n");
#endif
  noll_lemma_array *lemmas = noll_lemma_getpred (pid);
  if (lemmas == NULL)
    {
#ifndef NDEBUG
      NOLL_DEBUG ("\nNo lemma for pred-%d, syntactic matching fails!\n", pid);
#endif
      return NULL;
    }
  for (uint_t li = 0; li < noll_vector_size (lemmas); li++)
    {
      noll_lemma_t *lemma_i = noll_vector_at (lemmas, li);
      res = noll_shom_match_lemma (g2, pid, lemma_i, args2, eid1);
      if (res != NULL)
        {
#ifndef NDEBUG
          NOLL_DEBUG ("\nSyntactic matching lemma %d!\nmap found: ", li);
          noll_uid_map_fprint (stderr, res);
#endif
          break;
        }
    }
  return res;
}

/**
 * Apply the procedure based on syntactic checking for the fragment of
 * composable recursive definitions.
 */
int
noll_shom_check_syn (noll_graph_t * g2, noll_edge_t * e1,
                     noll_uid_array * args2)
{
  if (noll_pred_is_one_dir (e1->label) == false)
    {
      // special case of definitions with `previous' fields, NYI
#ifndef NDEBUG
      NOLL_DEBUG ("\nFail to check entailment: definition NYI\n");
#endif
      return 0;
    }
  /// initialise lemma, if not already done
  noll_lemma_init_pred (e1->label);

  /// Call the special function of the predicate and 
  /// collect the mapped edges of g2 in order to 
  /// check that all edges of g2 has been used.
  noll_uid_array *usedg2 = noll_shom_match_rd (g2, e1->label, args2, e1->id);
  int res = 1;
  if (usedg2 != NULL)
    {
      // check that all edges of g2 are used
      for (uint_t ei2 = 0;
           (ei2 < noll_vector_size (g2->edges)) && (res == 1); ei2++)
        {
          if (noll_vector_at (usedg2, ei2) == UNDEFINED_ID)
            {
#ifndef NDEBUG
              NOLL_DEBUG ("\nFailed check: edge %d not used\n", ei2);
#endif
              res = 0;
            }
        }
      noll_uid_array_delete (usedg2);
    }
  else
    {
      res = -1;                 // UNKNOWN
    }
  return res;
}

/**
 * Build the ls_hom component of the homeomorphism
 * which maps all ls edges in @p g1 to subgraphs in @p g2
 * such that the labeling with fields is respected.
 * Mark the mapped edges of @p g2 in usedg2.
 *
 * The graphs is the @return are subgraphs of g2
 * such that they contain only the edges mapped.
 *
 * @param g1     domain graph for the homeomorphism (in)
 * @param g2     co-domain graph (in)
 * @param n_hom  node mapping (in)
 * @param usedg2 mapping of edges in g2 to edges of g1
 * @param res    store the status of the result (0 if no mapping, 1 if mapping, -1 if unknown)
 * @return       the mapping built, NULL otherwise
 */
noll_graph_array *
noll_shom_build_rd (noll_graph_t * g1, noll_graph_t * g2,
                    noll_uid_map * n_hom, noll_uid_array * usedg2, int *res)
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
  for (uint_t i = 0; i < sz; i++)
    {
      // the edge to be mapped is at position t[sz - 1 - i]
      uint_t e1id = t[sz - 1 - i];
      noll_edge_t *e1 = noll_vector_at (g1->edges, e1id);
      e1->id = e1id;            // TO FIX now the order of edges
      if (e1->kind == NOLL_EDGE_PTO)
        break;                  /* because all PTO edges are at the end */
      /* translate the arguments of e1 using the node morphism */
      /* if predicate uses 'nil' then add nil as last (border) argument */
      noll_uid_array *args2 = noll_uid_map_apply (n_hom, e1->args,
                                                  noll_pred_use_nil
                                                  (e1->label));
      /* select the subgraph for edge e1
       * and also set usedg2 with the selected edges */
      noll_graph_t *sg2 =
        noll_shom_select_rd (g2, e1id, e1->label, args2, usedg2);
      if (sg2 == NULL)
        {                       /* free the allocated memory */
          noll_graph_array_delete (ls_hom);
          ls_hom = NULL;
          *res = 0;
#ifndef NDEBUG
          fprintf (stdout, "\nshom_ls: fails (select)!\n");
#endif
          if (noll_option_is_diag () == true)
            {
              fprintf (stdout, "\nDiagnosis of failure: ");
              fprintf (stdout, "\n\tConstraint not entailed: %s(%s,%s,...)\n",
                       noll_pred_name (e1->label),
                       noll_var_name (g2->lvars,
                                      noll_graph_get_var (g2,
                                                          noll_vector_at
                                                          (e1->args, 0)),
                                      NOLL_TYP_RECORD),
                       noll_var_name (g2->lvars,
                                      noll_graph_get_var (g2,
                                                          noll_vector_at
                                                          (e1->args, 1)),
                                      NOLL_TYP_RECORD));
              fprintf (stdout, "\t(empty selection of space constraints).\n");
            }
          // Warning: usedg2 is deselected also
          goto return_shom_ls;
        }
      /* check well-formedness of the selection */
      uint_t isdll =
        (0 == strncmp (noll_pred_name (e1->label), "dll", 3)) ? 1 : 0;
      if (0 == noll_shom_select_wf (g2, sg2, args2, isdll))
        {                       /* free the allocated memory */
          noll_graph_array_delete (ls_hom);
          ls_hom = NULL;
          *res = 0;
#ifndef NDEBUG
          fprintf (stdout, "\nshom_ls: fails (well-formedness)!\n");
#endif
          if (noll_option_is_diag () == true)
            {
              fprintf (stdout, "\nDiagnosis of failure: ");
              fprintf (stdout, "\n\tConstraint not entailed: %s(%s,%s,...)\n",
                       noll_pred_name (e1->label),
                       noll_var_name (g2->lvars,
                                      noll_graph_get_var (g2,
                                                          noll_vector_at
                                                          (e1->args, 0)),
                                      NOLL_TYP_RECORD),
                       noll_var_name (g2->lvars,
                                      noll_graph_get_var (g2,
                                                          noll_vector_at
                                                          (e1->args, 1)),
                                      NOLL_TYP_RECORD));
              fprintf (stdout,
                       "\t(selected space constraints not well formed).\n");
            }
          // Warning: usedg2 is deselected also
          goto return_shom_ls;
        }
      /* check entailment */
      *res = noll_shom_check (sg2, e1, args2);
      if (1 != *res)
        {                       /* free the allocated memory */
          noll_graph_array_delete (ls_hom);
          ls_hom = NULL;
          // *res is set above
#ifndef NDEBUG
          fprintf (stdout, "\nshom_ls: fails (code %d)!\n", *res);
#endif
          if (noll_option_is_diag () == true)
            {
              fprintf (stdout, "\nDiagnosis of failure: code %d (%s)",
                       *res, (*res == 0) ? "unvalid" : "unknown");
              fprintf (stdout, "\n\tConstraint not entailed: %s(%s,%s,...)\n",
                       noll_pred_name (e1->label),
                       noll_var_name (g2->lvars,
                                      noll_graph_get_var (g2,
                                                          noll_vector_at
                                                          (e1->args, 0)),
                                      NOLL_TYP_RECORD),
                       noll_var_name (g2->lvars,
                                      noll_graph_get_var (g2,
                                                          noll_vector_at
                                                          (e1->args, 1)),
                                      NOLL_TYP_RECORD));
              fprintf (stdout,
                       "\t(selected space constraints do not entail the above constraint).\n");
            }
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
 * @brief Build a homeomorphism from the @p i-th rhs graph.
 *
 * The homeomorphism maps noll_prob->ngraph[i] to noll_prob->pgraph.
 * Store the found mapping in hs->shom[i].
 *
 * @param hs   the homeomorphism to be built
 * @param i    the source graph to be considered
 * @return     1 if found, -1 if incomplete, 0 otherwise
 */
int
noll_shom_build (noll_hom_t * hs, size_t i)
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
  noll_uid_map *n_hom = NULL;
  noll_uid_array *usedg2 = NULL;
  noll_uid_array *pto_hom = NULL;
  noll_graph_array *ls_hom = NULL;

  /*
   * Build the mapping of nodes wrt variable labeling,
   * n_hom[n1] = n2 with n1 in g1, n2 in g2, n1, n2 node ids
   */
  n_hom = noll_shom_build_nodes (g1, g2);
  if (n_hom == NULL)
    {
      res = 0;
      goto return_shom;
    }

  /* Mapping of edges: special case of emp graph */
  if (noll_vector_size (g1->edges) == 0)
    {
      // the g2 shall also be empty
      if (noll_vector_size (g2->edges) != 0)
        {
          res = 0;
          goto return_shom;
        }
      pto_hom = noll_uid_array_new ();
      ls_hom = noll_graph_array_new ();
      usedg2 = noll_uid_array_new ();
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
  usedg2 = noll_uid_map_new (noll_vector_size (g2->edges));

  /*
   * Build the mapping of points-to edges to points-to edges
   * pto_hom[e1] = e2
   * with ei pto edge in gi, i=1,2
   */
  pto_hom = noll_shom_build_pto (g1, g2, n_hom, usedg2);
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
   *      g2' wellformed wrt e1 in g2
   */
  ls_hom = noll_shom_build_rd (g1, g2, n_hom, usedg2, &res);
  if (ls_hom == NULL)
    {
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
   * @see noll_hom_build_lseg
   */

return_shom:
  /* free allocated memory if the homeomorphism can not be built */
  if (res != 1)
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
  h->is_empty = (res != 1) ? true : false;
  h->node_hom = (res != 1) ? NULL : n_hom->data_;
  h->pto_hom = (res != 1) ? NULL : pto_hom;
  h->ls_hom = (res != 1) ? NULL : ls_hom;
  h->pused = (res != 1) ? NULL : usedg2;
  // push hom found in hs
  if (hs->is_empty)
    hs->is_empty = false;
  assert (NULL != hs->shom);
  assert (i < noll_vector_size (hs->shom));
  noll_vector_at (hs->shom, i) = h;

  /* TODO: to be changed for disjunctions */
  return res;
}
