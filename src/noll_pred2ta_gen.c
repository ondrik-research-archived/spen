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
#include "noll_pred2ta.h"


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
  /* the actual parameters are edge->args, 
   * @see noll_graph.h */

  /* the matrix of the predicate is stored in
   * pred->def->sigma0 (points-to)
   * pred->def->sigma1 (nested predicate calls)
   */

  NOLL_DEBUG ("Exposing the predicate matrix:\n\t- pto part:\n");
#ifndef NDEBUG
  noll_space_fprint (stdout, pred->def->vars, NULL, pred->def->sigma_0);
  fflush (stdout);
#endif

  NOLL_DEBUG ("\n\t- nested calls part:\n");
#ifndef NDEBUG
  noll_space_fprint (stdout, pred->def->vars, NULL, pred->def->sigma_1);
  fflush (stdout);
#endif

  return NULL;                  /* TODO */
}
