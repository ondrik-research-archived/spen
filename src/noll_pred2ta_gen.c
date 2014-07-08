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
#include "noll_ta_symbols.h"



/**
 * Translate the variables in the alias symbol using the mapping @param map.
 * 
 * @param sym     A symbol to be renamed
 * @param map     the mapping used for vars
 * @return        A new symbol
 */
noll_ta_symbol_t *
noll_pred2ta_translate_var (noll_ta_symbol_t * sym, noll_uid_array * map)
{
  return sym;                   // TODO
}


/**
 * Translate the node symbols in the parameters of the predicate 
 * with the markings given by the @param ta.
 * 
 * @param sym     A symbol to be renamed
 * @param ta      The TA with node markings
 * @return        A new symbol
 */
noll_ta_symbol_t *
noll_pred2ta_translate_pred (noll_ta_symbol_t * sym, noll_ta_t * ta)
{
  return sym;                   // TODO
}


/**
 * Get the TA for the @p edge.
 *
 * @param edge    A predicate edge
 * @return        A TA recognizing the tree encodings for this edge
 */
noll_ta_t *
noll_edge2ta_gen (const noll_edge_t * edge)
{
  assert (NULL != edge);
  assert (NOLL_EDGE_PRED == edge->kind);
  assert (2 <= noll_vector_size (edge->args));

  /* identifier of the predicate */
  const uid_t pid = edge->label;
  /* informations about the predicate in the global table */
  const noll_pred_t *pred = noll_pred_getpred (edge->label);
  /* check that these informations are filled and correct */
  assert (NULL != pred);
  assert (NULL != pred->pname);
  assert (NULL != pred->def);
  assert (noll_vector_size (edge->args) == pred->def->fargs);

  /* the formal parameters are in pred->def->vars[1,pred->def->fargs], 
   * @see noll_preds.h */
  /* the actual parameters (their identifiers) are in edge->args, 
   * @see noll_graph.h */
  /* the matrix of the predicate is stored in
   * pred->def->sigma0 (points-to)
   * pred->def->sigma1 (nested predicate calls)
   */

#ifndef NDEBUG
  fprintf (stdout, "Exposing the predicate matrix:\n\t- pto part:\n");
  noll_space_fprint (stdout, pred->def->vars, NULL, pred->def->sigma_0);
  fprintf (stdout, "\n\t- nested calls part:\n");
  noll_space_fprint (stdout, pred->def->vars, NULL, pred->def->sigma_1);
  fflush (stdout);
#endif

  /*
   * Build a graph from the predicate matrix by calling noll_graph_of_form
   * - first build the formula matrix(in,x_tl) * matrix (x_tl,out)
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
  /* 
   * To create the tree, we need the homomorphism mapping 
   * the i-th argument to a node in the graph.
   * Because the formal args are in the gp->lvars, starting with null,
   * then with first arg, etc., we add +1 to index of arg.
   */
  noll_uid_array *hid = noll_uid_array_new ();
  /* push node of the first arg */
  noll_uid_array_push (hid, gp->var2node[1]);
  /* push node of the second arg */
  noll_uid_array_push (hid, gp->var2node[2]);
  /* push nodes for border args */
  for (size_t i = 2; i < noll_vector_size (edge->args); i++)
    noll_uid_array_push (hid, gp->var2node[i + 1]);
  /* create the TA for this graph */
  noll_tree_t *treep = noll_graph2ta (gp, hid);
#ifndef NDEBUG
  fprintf (stdout, "\n- tree of matrix\n");
  noll_tree_fprint (stdout, treep);
  fflush (stdout);
#endif


  NOLL_DEBUG ("\nBuild the TA recognizing the tree\n");
  /* node identifiers */
  uid_t initial_node = gp->var2node[1];
  uid_t end_node = gp->var2node[2];
  uid_t x_tl_node = gp->var2node[1 + noll_vector_size (edge->args)];

#ifndef NDEBUG
  fprintf (stdout, "- initial_node = node(%d)\n", initial_node);
  fprintf (stdout, "- x_tl__node = node(%d)\n", x_tl_node);
  fprintf (stdout, "- end_node = node(%d)\n", end_node);
  fflush (stdout);
#endif

  /* 1) Skeleton of TA */
  vata_ta_t *tap = NULL;
  if ((tap = vata_create_ta ()) == NULL)
    {
      return NULL;
    }
  /* set the root = rot of tree */
  vata_set_state_root (tap, treep->root);

  /* For each node of the tree */
  for (size_t i = 0; i < noll_vector_size (treep->nodes); ++i)
    {
      const noll_tree_node_t *node = noll_vector_at (treep->nodes, i);
      if (NULL == node)
        /* some nodes are not filled in the tree, e.g., null */
        continue;

      assert (NULL != node->symbol);

      NOLL_DEBUG ("\n\t- node symbol <%s>\n",
                  noll_ta_symbol_get_str (node->symbol));

      /* Alias transitions (6) */
      if (noll_ta_symbol_is_alias (node->symbol))
        {
          NOLL_DEBUG ("Node %d : alias\n", i);
          /* rename formal param to actual parameter */
          noll_ta_symbol_t *asymbol =
            noll_pred2ta_translate_var (node->symbol, NULL);
          vata_add_transition (tap, i, asymbol, NULL);
        }
      /* Predicate transitions (7) */
      else if (noll_ta_symbol_is_pred (node->symbol))
        {
          NOLL_DEBUG ("Node %d : pred\n", i);
          /* rename node symbol arguments with markings wrt source node */
          noll_ta_symbol_t *asymbol =
            noll_pred2ta_translate_pred (node->symbol, NULL);
          vata_add_transition (tap, i, asymbol, node->children);
        }
      /* Points-to edges (8)(9) */
      else if (noll_ta_symbol_is_pto (node->symbol))
        {
          NOLL_DEBUG ("Node %d : pto\n", i);
          if (i == treep->root)
            {
              NOLL_DEBUG ("Node %d (root): add pto loops in %d\n", i,
                          x_tl_node);
              // Transitions (9')
              vata_add_transition (tap, x_tl_node,
                                   noll_vector_at (treep->nodes,
                                                   x_tl_node)->symbol,
                                   node->children);
            }
          if (i == x_tl_node)
            {
              NOLL_DEBUG ("Node %d: add pto in %d\n", i, initial_node);
              // Transitions (9'')
              /* rename formal param to actual parameter */
              noll_ta_symbol_t *asymbol =
                noll_pred2ta_translate_var (noll_vector_at (treep->nodes,
                                                            initial_node)->
                                            symbol, NULL);
              vata_add_transition (tap, initial_node, asymbol,
                                   node->children);
            }
          // Transitions (8)
          vata_add_transition (tap, i, node->symbol, node->children);
        }
    }

  /* Transitions (10) */
  NOLL_DEBUG ("Node %d: add alias to 2nd arg\n", end_node);
  const noll_ta_symbol_t *end_symbol =
    noll_ta_symbol_get_unique_aliased_var (noll_vector_at (edge->args, 1));

  vata_add_transition (tap, end_node, end_symbol, NULL);

  /* Transitions (13)(14)(15) */
  /* label of in variables */
  noll_uid_array *vars_brd = noll_uid_array_new ();
  assert (NULL != vars_brd);
  for (size_t i = 2; i < noll_vector_size (edge->args); i++)
    /* vars in gp are starting with null, add +1 */
    noll_uid_array_push (vars_brd, gp->var2node[i + 1]);

  /* empty marking for the first state */
  noll_uid_array *mark_eps = noll_uid_array_new ();
  assert (NULL != mark_eps);
  noll_uid_array_push (mark_eps, NOLL_MARKINGS_EPSILON);

  noll_uid_array *pred_children1 = noll_uid_array_new ();
  noll_uid_array *pred_children2 = noll_uid_array_new ();

  const noll_ta_symbol_t *pred_symbol =
    noll_ta_symbol_get_unique_higher_pred (pred, vars_brd, mark_eps);
  assert (NULL != pred_symbol);
  /* rename node symbol arguments with markings wrt source node */
  noll_ta_symbol_t *pred_symbol_a =
    noll_pred2ta_translate_pred (pred_symbol, NULL);
  noll_uid_array_push (pred_children1, x_tl_node);
  noll_uid_array_push (pred_children2, end_node);

  // Transitions (13)
  vata_add_transition (tap, x_tl_node, pred_symbol_a, pred_children1);
  // Transitions (15)
  // TODO: rename initial node marking
  vata_add_transition (tap, initial_node, pred_symbol_a, pred_children1);
  // Transitions (14)
  vata_add_transition (tap, x_tl_node, pred_symbol_a, pred_children2);

  noll_uid_array_delete (mark_eps);
  noll_uid_array_delete (pred_children1);
  noll_uid_array_delete (pred_children2);

  /* TODO: add nested TA for nested calls */

  return tap;
}
