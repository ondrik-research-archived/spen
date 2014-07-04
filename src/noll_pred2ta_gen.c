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
 * Defines translation between heap graph to tree automata 
 * for any predicate definition.
 */

#include "noll.h"
#include "libvata_noll_iface.h"
#include "noll2graph.h"
#include "noll_pred2ta.h"
#include "noll_graph2ta.h"


/**
 * Get the TA for the @p edge.
 *
 * @param edge    A predicate edge
 * @return        A TA recorgnizing the tree encodings for this edge
 */
noll_ta_t *
noll_edge2ta_gen (const noll_edge_t * edge)
{
  assert (NULL != edge);
  assert (NOLL_EDGE_PRED == edge->kind);
  assert (2 <= noll_vector_size (edge->args));

  /* identifier of the predicate */
  const uid_t pid = edge->label;
  /* get all informations about the predicate in the global table */
  const noll_pred_t *pred = noll_pred_getpred (edge->label);
  /* check that these informations are filled and correct */
  assert (NULL != pred);
  assert (NULL != pred->pname);
  assert (NULL != pred->def);
  assert (noll_vector_size (edge->args) == pred->def->fargs);

  /* the formal parameters are in 
   * pred->def->vars[1,pred->def->fargs], 
   * @see noll_preds.h */
  /* the identifiers of the actual parameters are edge->args, 
   * @see noll_graph.h */

  /* the matrix of the predicate is stored in
   * pred->def->sigma0 (points-to)
   * pred->def->sigma1 (nested predicate calls)
   */

#ifndef NDEBUG
  fprintf (stdout, "Exposing the predicate matrix:\n\t- pto part:\n");
  noll_space_fprint (stdout, pred->def->vars, NULL, pred->def->sigma_0);
  fflush (stdout);
#endif

#ifndef NDEBUG
  fprintf (stdout, "\n\t- nested calls part:\n");
  noll_space_fprint (stdout, pred->def->vars, NULL, pred->def->sigma_1);
  fflush (stdout);
#endif

  /*
   * Build a graph from the predicate matrix by calling noll_graph_of_form
   * - first build a formula
   * - then call noll_graph_of_form
   */
#ifndef NDEBUG
  fprintf (stdout, "\nBuild the graph of the predicate matrix\n");
#endif
  noll_form_t *phip = noll_pred_get_matrix (pid);
  noll_graph_t *gp = noll_graph_of_form (phip);
  assert ((noll_vector_size (edge->args) + 1) <=
          noll_vector_size (gp->lvars));
#ifndef NDEBUG
  fprintf (stdout, "\n- graph of matrix\n");
  noll_graph_fprint (stdout, gp);
  fflush (stdout);
#endif

  NOLL_DEBUG ("\nBuild the tree of the predicate matrix\n");
  /* create the homomorphism mapping formal params to actual params */
  noll_uid_array *hid = noll_uid_array_new ();
  /* for src push first arg also */
  noll_uid_array_push (hid, gp->var2node[1]);
  /* for dst push second arg */
  noll_uid_array_push (hid, gp->var2node[2]);
  /* for border push border */
  for (size_t i = 2; i < noll_vector_size (edge->args); i++)
    /* vars in gp are starting with null, add +1 */
    noll_uid_array_push (hid, gp->var2node[i + 1]);
  /* create the TA for this graph with the identity homomorpshims */
  noll_tree_t *treep = noll_graph2ta (gp, hid);
#ifndef NDEBUG
  fprintf (stdout, "\n- tree of matrix\n");
  noll_tree_fprint (stdout, treep);
  fflush (stdout);
#endif

  noll_ta_t *tap = noll_tree_to_ta (treep);     /* TODO */

  return tap;                   /* TODO */
}
