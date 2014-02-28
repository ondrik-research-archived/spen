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

#include <limits.h>

#include "noll.h"
#include "noll_graph2ta.h"
#include "noll_ta_symbols.h"
#include "noll_vector.h"
#include "libvata_noll_iface.h"

/* ====================================================================== */
/* Data types */
/* ====================================================================== */

// a list of markings (associated to very node)
NOLL_VECTOR_DECLARE( noll_marking_list, noll_uid_array* )
NOLL_VECTOR_DEFINE( noll_marking_list, noll_uid_array* )

// mapping of nodes to lists of their markings
NOLL_VECTOR_DECLARE( noll_nodes_to_markings , noll_marking_list* )
NOLL_VECTOR_DEFINE( noll_nodes_to_markings , noll_marking_list* )

/* ====================================================================== */
/* Macros */
/* ====================================================================== */

#define MIN(x, y) (((x) > (y))? (y) : (x))

/* ====================================================================== */
/* Constants */
/* ====================================================================== */

static const uid_t NOLL_MARKINGS_EPSILON = -1;
static const uid_t initial_node = 0;

/* ====================================================================== */
/* Globals */
/* ====================================================================== */

static size_t noll_unique_cnt = 42;

static size_t noll_get_unique(void)
{
	assert(noll_unique_cnt < SSIZE_MAX);

	return noll_unique_cnt++;
}


/* ====================================================================== */
/* Debugging functions */
/* ====================================================================== */

static void noll_debug_print_one_mark(const noll_uid_array* mark)
{
	if (NULL == mark)
	{
		NOLL_DEBUG("NULL");
		return;
	}

	NOLL_DEBUG("[");
	for (size_t i = 0; i < noll_vector_size(mark); ++i)
	{
		if (i != 0)
		{
			NOLL_DEBUG(", ");
		}

		NOLL_DEBUG("%d", noll_vector_at(mark, i));
	}
	NOLL_DEBUG("]");
}


/**
 * @brief  Debugging output of markings
 *
 * @param[in]  markings  The markings to be printed
 */
static void noll_debug_print_markings(const noll_marking_list* markings)
{
	assert(NULL != markings);

	for (size_t j = 0; j < noll_vector_size(markings); ++j)
	{
		const noll_uid_array* mark = noll_vector_at(markings, j);
		assert(NULL != mark);
		NOLL_DEBUG("Node %lu: ", j);
		noll_debug_print_one_mark(mark);
		NOLL_DEBUG("\n");
	}
}


/* ====================================================================== */
/* Auxiliary functions */
/* ====================================================================== */


/**
 * @brief  Determines the longest common prefix of a pair of markings
 *
 * @param[in]  lhs  The first marking
 * @param[in]  rhs  The other marking
 *
 * @returns  The longest common prefix of @p lhs and @p rhs. The caller is
 *           responsible for the deallocation of the returned structure.
 */
static noll_uid_array* noll_longest_common_prefix(
	const noll_uid_array*   lhs,
	const noll_uid_array*   rhs)
{
	assert(NULL != lhs);
	assert(NULL != rhs);

	noll_uid_array* lcp = noll_uid_array_new();
	assert(NULL != lcp);

	size_t size_shorter = MIN(noll_vector_size(lhs), noll_vector_size(rhs));

	for (size_t i = 0; i < size_shorter; ++i)
	{
		if (noll_vector_at(lhs, i) != noll_vector_at(rhs, i))
		{
			break;
		}

		noll_uid_array_push(lcp, noll_vector_at(lhs, i));
	}

	return lcp;
}


/**
 * @brief  Does the array contain the given element?
 *
 * Checks for the presence of the element @p elem in the (unordered) array @p
 * arr.
 *
 * @param[in]  arr   The array to check
 * @param[in]  elem  The element to check for
 *
 * @returns  @p true iff @p arr contains @p elem, @p false otherwise
 */
static bool noll_uid_array_contains(
	const noll_uid_array*     arr,
	uid_t                     elem)
{
	assert(NULL != arr);

	for (size_t i = 0; i < noll_vector_size(arr); ++i)
	{
		if (noll_vector_at(arr, i) == elem)
		{
			return true;
		}
	}

	return false;
}


/**
 * @brief  Implementation of the <= relation over record fields
 *
 * @param[in]  lhs  The left hand side field
 * @param[in]  rhs  The right hand side field
 *
 * @returns  @p true iff lhs < rhs w.r.t. the field ordering, @p false
 *           otherwise
 */
static bool noll_fields_order_lt(
	uid_t            lhs,
	uid_t            rhs)
{
	if ((&rhs != &rhs) || (&lhs != &lhs))
	{
		assert(false);
	}

	NOLL_DEBUG("WARNING: %s() approximating to TRUE\n", __func__);

	return true;
}


static bool noll_fields_is_backbone(
	uid_t            field)
{
	if (&field != &field)
	{
		assert(false);
	}

	NOLL_DEBUG("WARNING: %s() approximating to TRUE\n", __func__);

	return true;
}


/**
 * @brief  Implementation of the <= relation over nodes' markings
 *
 * @param[in]  lhs  The left hand side marking
 * @param[in]  rhs  The right hand side marking
 *
 * @returns  @p true iff lhs <= rhs w.r.t. the marking ordering, @p false
 *           otherwise
 */
static bool noll_marking_order_lt(
	const noll_uid_array*      lhs,
	const noll_uid_array*      rhs)
{
	assert(NULL != lhs);
	assert(NULL != rhs);
	if ((&rhs != &rhs) || (&lhs != &lhs))
	{
		assert(false);
	}

	NOLL_DEBUG("WARNING: %s() approximating to TRUE\n", __func__);

	return true;
}


/**
 * @brief  The "marking is a prefix or equal" predicate
 *
 * This binary predicate holds true iff @p pred is a prefix (not necessarily
 * proper) of @p succ.
 *
 * @param[in]  pred  The potential predecessor
 * @param[in]  succ  The potential successor
 *
 * @returns  @p true iff @p pred is a prefix of @p succ
 */
bool noll_marking_is_prefix_or_equal(
	const noll_uid_array*      pred,
	const noll_uid_array*      succ)
{
	// check for sanity of the inputs
	assert(NULL != pred);
	assert(NULL != succ);

	if (noll_vector_size(pred) > noll_vector_size(succ))
	{	// if the lengths are wrong
		return false;
	}

	for (size_t i = 0; i < noll_vector_size(pred); ++i)
	{	// check that 'succ' is the same as 'pred' up to the length of 'pred'
		if (noll_vector_at(pred, i) != noll_vector_at(succ, i))
		{
			return false;
		}
	}

	return true;
}


/**
 * @brief  Computes markings of nodes of a graph
 *
 * Given a @p graph, this function computes the minimum marker for every node
 * of @p graph, which is stored into @p markings. In the case the computation
 * failed at some point (such as when there is a disconnected node in the
 * graph), the function returns @p false, otherwise (if the computation was
 * successful), the function returns @p true.
 *
 * @param[in]   graph     The input graph
 * @param[out]  markings  The computed markings
 *
 * @returns  @p true if the computation was successful, @p false otherwise
 */
static bool compute_markings(
	const noll_graph_t*     graph,
	noll_marking_list*      markings)
{
	assert(NULL != graph);
	assert(NULL != markings);

	size_t num_nodes = graph->nodes_size;
	assert(0 < num_nodes);
	noll_marking_list_resize(markings, num_nodes);

	noll_nodes_to_markings* nodes_to_markings = noll_nodes_to_markings_new();
	assert(NULL != nodes_to_markings);
	noll_nodes_to_markings_resize(nodes_to_markings, num_nodes); // resize should allocate enough mem
	for (size_t i = 0; i < noll_vector_size(nodes_to_markings); ++i)
	{	// we allocate empty list of markings for every node now
		NOLL_DEBUG("Allocating marking for node %lu\n", i);
		noll_vector_at(nodes_to_markings, i) = noll_marking_list_new();
		assert(NULL != noll_vector_at(nodes_to_markings, i));
	}

	// TODO: consider other initial node that the one with number 0
	NOLL_DEBUG("WARNING: we assume the index of the initial node of the graph is 0\n");
	assert(initial_node < num_nodes);

	NOLL_DEBUG("Computing marking of nodes of the graph\n");

	// initialize the marking of the initial node to be 'epsilon'
	// TODO: the NOLL_MARKINGS_EPSILON symbol is useless here, but it makes some
	// things easier (such as that *_last() will not fail)
	noll_uid_array* epsilon_marking = noll_uid_array_new();
	assert(NULL != epsilon_marking);
	noll_uid_array_push(epsilon_marking, NOLL_MARKINGS_EPSILON);
	noll_marking_list* initial_node_markings = noll_vector_at(nodes_to_markings, initial_node);
	assert(NULL != initial_node_markings);
	noll_marking_list_push(initial_node_markings, epsilon_marking);

	bool changed = true;
	while (changed)
	{	// until we reach a fixed point
		changed = false;

		for (size_t i = 0; i < noll_vector_size(graph->edges); ++i)
		{	// go over all edges and update according to them
			const noll_edge_t* edge = noll_vector_at(graph->edges, i);
			assert(NULL != edge);
			assert(2 == noll_vector_size(edge->args));
			NOLL_DEBUG("Processing edge (*g->edges)[%lu] = %p, ", i, edge);
			NOLL_DEBUG("from = %u, to = %u, id = %u, kind = %u, label = %u\n",
				noll_vector_at(edge->args, 0),
				noll_vector_at(edge->args, 1),
				edge->id,
				edge->kind,
				edge->label);

			// check that the nodes are in the correct range
			assert(noll_vector_at(edge->args, 0) < num_nodes);
			assert(noll_vector_at(edge->args, 1) < num_nodes);

			// get markings of the source and destination nodes
			const noll_marking_list* src_markings = noll_vector_at(nodes_to_markings,
				noll_vector_at(edge->args, 0));
			noll_marking_list* dst_markings = noll_vector_at(nodes_to_markings,
				noll_vector_at(edge->args, 1));
			for (size_t j = 0; j < noll_vector_size(src_markings); ++j)
			{
				noll_uid_array* new_marking = noll_uid_array_new();
				noll_uid_array_copy(new_marking, noll_vector_at(src_markings, j));
				assert(0 < noll_vector_size(new_marking));
				if ((noll_vector_last(new_marking) == edge->label)
					&& noll_fields_is_backbone(edge->label))
				{
					// we keep the same marking
				}
				else if (noll_fields_order_lt(noll_vector_last(new_marking), edge->label))
				{
					// we add the field at the end of the marking
					noll_uid_array_push(new_marking, edge->label);
				}
				else
				{
					assert(false);       // fail gracefully
				}

				bool found = false;
				for (size_t k = 0; k < noll_vector_size(dst_markings); ++k)
				{	// check whether the marking is not already there
					const noll_uid_array* dst_mark = noll_vector_at(dst_markings, k);
					assert(NULL != dst_mark);
					if (noll_uid_array_equal(new_marking, dst_mark))
					{
						found = true;
						break;
					}
				}

				if (!found)
				{
					changed = true;
					noll_marking_list_push(dst_markings, new_marking);
				}
				else
				{
					noll_uid_array_delete(new_marking);
				}
			}
		}
	}

	NOLL_DEBUG("Marking of nodes of the graph computed\n");
	NOLL_DEBUG("Markings:\n");

	// print the computed markings
	for (size_t i = 0; i < noll_vector_size(nodes_to_markings); ++i)
	{
		const noll_marking_list* list = noll_vector_at(nodes_to_markings, i);
		assert(NULL != list);
		NOLL_DEBUG("Node %lu: {", i);
		for (size_t j = 0; j < noll_vector_size(list); ++j)
		{
			noll_debug_print_one_mark(noll_vector_at(list, j));
			NOLL_DEBUG(", ");
		}
		NOLL_DEBUG("}\n");
	}

	// compute the least marking for every node
	bool is_fine = true;
	for (size_t i = 0; i < noll_vector_size(nodes_to_markings); ++i)
	{
		NOLL_DEBUG("Going over node %lu\n", i);
		const noll_marking_list* list = noll_vector_at(nodes_to_markings, i);
		assert(NULL != list);
		if (0 == noll_vector_size(list))
		{	// if there is a node with no marking
			is_fine = false;
			break;
		}

		assert(noll_vector_size(list) > 0);
		noll_uid_array** ptr_least_marking = &noll_vector_at(list, 0);
		assert(NULL != ptr_least_marking);
		assert(NULL != *ptr_least_marking);
		for (size_t j = 1; j < noll_vector_size(list); ++j)
		{
			noll_uid_array** mark = &noll_vector_at(list, j);
			assert(NULL != mark);
			assert(NULL != *mark);
			if (noll_marking_order_lt(*mark, *ptr_least_marking))
			{
				ptr_least_marking = mark;
			}
		}

		noll_vector_at(markings, i) = *ptr_least_marking;
		*ptr_least_marking = NULL;
	}

	NOLL_DEBUG("Before killing\n");
	// print the computed markings
	for (size_t i = 0; i < noll_vector_size(nodes_to_markings); ++i)
	{
		const noll_marking_list* list = noll_vector_at(nodes_to_markings, i);
		assert(NULL != list);
		NOLL_DEBUG("Node %lu: {", i);
		for (size_t j = 0; j < noll_vector_size(list); ++j)
		{
			noll_debug_print_one_mark(noll_vector_at(list, j));
			NOLL_DEBUG(", ");
		}
		NOLL_DEBUG("}\n");
	}

	// delete markings
	for (size_t i = 0; i < noll_vector_size(nodes_to_markings); ++i)
	{	// we allocate empty markings for every node now
		noll_marking_list* list = noll_vector_at(nodes_to_markings, i);
		assert(NULL != list);
		for (size_t j = 0; j < noll_vector_size(list); ++j)
		{
			if (NULL != noll_vector_at(list,j))
			{
				noll_uid_array_delete(noll_vector_at(list, j));
			}
		}
		noll_marking_list_delete(list);
	}
	noll_nodes_to_markings_delete(nodes_to_markings);

	return is_fine;
}


/**
 * @brief  Checks whether a marking corresponds to a successor of another one
 *
 * This function checks that the marking @p node_marking of some node @p n can
 * be achieved by extending the marking @p pred_marking of its predecessor @p p
 * with the symbol @p symbol. This is used to check whether @p symbol denotes
 * the @p backbone edge from @p n to @p p.
 *
 * @param[in]  node_marking  Marking of node @p n
 * @param[in]  pred_marking  Marking of node @p p
 * @param[in]  symbol        The symbol of the edge between @p p and @p n
 *
 * @returns  @p true if @p node_marking is the successor of @p prev_marking
 *           over the edge labelled with @p symbol
 */
static bool noll_marking_is_succ_of_via(
	const noll_uid_array*     node_marking,
	const noll_uid_array*     pred_marking,
	uid_t                     symbol)
{
	// check whether the parameters are sane
	assert(NULL != node_marking);
	assert(NULL != pred_marking);
	assert(0 != noll_vector_size(node_marking));
	assert(0 != noll_vector_size(pred_marking));

	NOLL_DEBUG("Testing whether marking [");
	for (size_t i = 0; i < noll_vector_size(node_marking); ++i)
	{
		NOLL_DEBUG("%d, ", noll_vector_at(node_marking, i));
	}
	NOLL_DEBUG("] is a successor of [");
	for (size_t i = 0; i < noll_vector_size(pred_marking); ++i)
	{
		NOLL_DEBUG("%d, ", noll_vector_at(pred_marking, i));
	}
	NOLL_DEBUG("] via %u: ", symbol);

	if (noll_vector_last(node_marking) != symbol)
	{	// in the case the last symbol of the marking is not the checked symbol
		NOLL_DEBUG("false\n");
		return false;
	}

	int diff = noll_vector_size(node_marking) - noll_vector_size(pred_marking);
	if ((0 != diff) && (1 != diff))
	{	// if the backboneness is impossible
		NOLL_DEBUG("false\n");
		return false;
	}

	for (size_t i = 0; i < noll_vector_size(pred_marking); ++i)
	{
		if (noll_vector_at(pred_marking, i) != noll_vector_at(node_marking, i))
		{	// in the case there is a mismatch
			NOLL_DEBUG("false\n");
			return false;
		}
	}

	NOLL_DEBUG("true\n");
	return true;
}


/**
 * @brief  A function checking that node @p dst is reachable from node @p src
 *
 * This function checks whether the node @p dst is reachable from the node @p
 * src in the @p graph along a path where the marker @p mark is not used (while
 * not including @p dst to this check).
 *
 * @param[in]  graph     The graph
 * @param[in]  markings  The markings of nodes of @p graph
 * @param[in]  dst       The destination node
 * @param[in]  src       The source node
 * @param[in]  mark      The marking to be checked for
 *
 * @returns  @p true iff @p dst is reachable from @p src on a path without @p
 *           mark
 */
static bool reachable_from_through_path_wo_marker(
	const noll_graph_t*          graph,
	const noll_marking_list*     markings,
	uid_t                        dst,
	uid_t                        src,
	const noll_uid_array*        mark)
{
	assert(NULL != graph);
	assert(NULL != mark);
	assert(src < graph->nodes_size);
	assert(dst < graph->nodes_size);

	noll_uid_array* workstack = noll_uid_array_new();
	assert(NULL != workstack);

	// an ordinary array for processed nodes
	noll_uid_array* processed = noll_uid_array_new();
	assert(NULL != processed);

	noll_uid_array_push(workstack, src);

	bool found_dst = false;
	while (!noll_vector_empty(workstack) && !found_dst)
	{
		uid_t node = noll_vector_last(workstack);
		noll_uid_array_pop(workstack);
		assert(node < graph->nodes_size);
		assert(!noll_uid_array_contains(processed, node));
		noll_uid_array_push(processed, node);

		NOLL_DEBUG("Testing node %u\n", node);

		const noll_uid_array* edges_from_node = graph->mat[node];
		if (NULL == edges_from_node)
		{	// in the case 'node' has no outgoing edges
			continue;
		}

		for (size_t i = 0; i < noll_vector_size(edges_from_node); ++i)
		{
			uid_t edge_id = noll_vector_at(edges_from_node, i);
			NOLL_DEBUG("Found edge %u\n", edge_id);

			const noll_edge_t* ed = noll_vector_at(
				graph->edges,
				noll_vector_at(edges_from_node, edge_id));
			assert(NULL != ed);
			assert(NOLL_EDGE_PTO == ed->kind);
			assert(2 == noll_vector_size(ed->args));
			assert(noll_vector_at(ed->args, 0) == node);
			uid_t post_node = noll_vector_at(ed->args, 1);

			if (post_node == dst)
			{	// if we found the destination
				found_dst = true;
				break;
			}

			if (noll_uid_array_equal(
				noll_vector_at(markings, post_node), mark))
			{	// if we hit 'mark', do not expand
				continue;
			}
		}
	}
	noll_uid_array_delete(workstack);
	noll_uid_array_delete(processed);

	return found_dst;
}


/* ====================================================================== */
/* Translators */
/* ====================================================================== */

/**
 *  Translates g into a tree automaton.
 *  @return TA built or NULL
 */
noll_ta_t* noll_graph2ta(noll_graph_t* g) {
	// check sanity of input parameters
	assert(NULL != g);
	assert(NULL != g->lvars);
	assert(NULL != g->svars);
	assert(NULL != g->var2node);
	assert(NULL != g->edges);

	NOLL_DEBUG("g = %p\n", g);
	NOLL_DEBUG("number of nodes in g = %d\n", g->nodes_size);
	NOLL_DEBUG("LVars:\n");
	for (size_t i = 0; i < noll_vector_size(g->lvars); ++i)
	{
		NOLL_DEBUG("  (*g->lvars)[%lu] = %p, ", i, noll_vector_at(g->lvars, i));
		const noll_var_t* var = noll_vector_at(g->lvars, i);
		assert(NULL != var);
		NOLL_DEBUG("name = %s, vid = %u, ", var->vname, var->vid);
		NOLL_DEBUG("points to node -> %u\n", g->var2node[i]);
	}
	NOLL_DEBUG("SVars:\n");
	for (size_t i = 0; i < noll_vector_size(g->svars); ++i)
	{
		NOLL_DEBUG("  (*g->svars)[%lu] = %p, ", i, noll_vector_at(g->svars, i));
		const noll_var_t* var = noll_vector_at(g->svars, i);
		assert(NULL != var);
		NOLL_DEBUG("name = %s, vid = %u, \n", var->vname, var->vid);
	}
	NOLL_DEBUG("Edges:\n");
	for (size_t i = 0; i < noll_vector_size(g->edges); ++i) {
		NOLL_DEBUG("  (*g->edges)[%lu] = %p, ", i, noll_vector_at(g->edges, i));
		const noll_edge_t* edge = noll_vector_at(g->edges, i);
		assert(NULL != edge);
		NOLL_DEBUG("from = %u, to = %u, id = %u, kind = %u, label = %u\n",
			noll_vector_at(edge->args, 0),
			noll_vector_at(edge->args, 1),
			edge->id,
			edge->kind,
			edge->label);
	}

	// Now, we compute for every node 'n' a set of markings 'pi(n)'. These is a
	// least fix point computation.

	// first, let's prepare a map of nodes to their markings, nodes are labelled
	// from 0, so let that be a vector

	noll_marking_list* markings = noll_marking_list_new();
	assert(NULL != markings);
	if (!compute_markings(g, markings))
	{	// in the case the computation of markings was not successful
		assert(false);            // fail gracefully
	}

	NOLL_DEBUG("Least markings:\n");

	// print the computed markings
	noll_debug_print_markings(markings);

	NOLL_DEBUG("Generating the TA for the graph\n");
  vata_ta_t* ta = NULL;
  if ((ta = vata_create_ta()) == NULL)
  {
    return NULL;
  }

	// set the initial node as the root state
	vata_set_state_root(ta, initial_node);

	// we transform the graph into a TA represting a tree (i.e. the language of
	// the TA is a singleton set) such that node 'i' is represented by the TA
	// state 'i'
	for (size_t i = 0; i < g->nodes_size; ++i)
	{
		const noll_uid_array* edges = g->mat[i];
		if (NULL == edges)
		{	// if there are no edges leaving 'i'
			NOLL_DEBUG("No edges leaving node %lu\n", i);
			continue;
		}

		noll_uid_array* children = noll_uid_array_new();
		assert(NULL != children);
		noll_uid_array* selectors = noll_uid_array_new();
		assert(NULL != selectors);
		noll_uid_array* vars = noll_uid_array_new();
		assert(NULL != vars);

		const noll_uid_array* mark_i = noll_vector_at(markings, i);
		assert(NULL != mark_i);

		for (size_t j = 0; j < noll_vector_size(edges); ++j)
		{
			const noll_edge_t* ed = noll_vector_at(g->edges, noll_vector_at(edges, j));
			assert(NULL != ed);
			assert(NOLL_EDGE_PTO == ed->kind);
			const char* field_name = noll_field_name(ed->label);
			NOLL_DEBUG("Edge from the node %lu: %p, %s\n", i, ed, field_name);
			assert(2 == noll_vector_size(ed->args));
			assert(noll_vector_at(ed->args, 0) == i);
			uid_t next_child = noll_vector_at(ed->args, 1);
			NOLL_DEBUG("Neighbour of the node %lu: %u\n", i, next_child);

			// marking of the child
			const noll_uid_array* mark_next_child = noll_vector_at(markings, next_child);
			assert(NULL != mark_next_child);

			// adding the selector
			noll_uid_array_push(selectors, ed->label);

			NOLL_DEBUG("Now, we check whether the edge %s is a backbone edge from %lu to %u\n", field_name, i, next_child);
			if (noll_marking_is_succ_of_via(mark_next_child, mark_i, ed->label))
			{	// if 'ed' is a backbone edge
				NOLL_DEBUG("We are on the backbone!\n");
				noll_uid_array_push(children, next_child);
			}
			else
			{	// If 'ed' is not a backbone edge. This means that the edge will not be
				// represented in the direct way, but needs to be represented using a
				// path that traverses the backbone in an indirect way. So we need to
				// classify the type of the needed path (there are only some
				// considered) and use a node labelled by this in the transition
				NOLL_DEBUG("We are NOT on the backbone...\n");

				NOLL_DEBUG("WARNING: not checking whether the node is marked by a program variable.\n");

				if (noll_marking_is_prefix_or_equal(mark_next_child, mark_i))
				{	// in the case the source is a predecessor of the target (this is the
					// case e.g. for a doubly-linked segment)
					NOLL_DEBUG("The source ");
					noll_debug_print_one_mark(mark_next_child);
					NOLL_DEBUG(" is a PREFIX of the target ");
					noll_debug_print_one_mark(mark_i);
					NOLL_DEBUG("\n");

					NOLL_DEBUG("Now, we check whether node %lu is reachable from node %u on a path that does not use the marking ", i, next_child);
					noll_debug_print_one_mark(mark_next_child);
					NOLL_DEBUG("\n");

					// TODO: first test marking, then the reachability
					if (reachable_from_through_path_wo_marker(
						g, markings, i, next_child, mark_next_child))
					{	// in case 'i' is reachable from 'next_child' via a path where the
						// marker '\mu(n)' is not used
						if (!noll_uid_array_equal(mark_next_child, mark_i))
						{	// in case $\mu(n') != \mu(n)$, mark the leaf with 's1(\mu(n))'
							NOLL_DEBUG("Detected an s1() marker\n");
							assert(false);

							// TODO: skip what follows

						}
						else
						{	// in case $\mu(n') = \mu(n)$, mark the leaf with 's2(\mu(n))'
							NOLL_DEBUG("Detected an s2() marker\n");
							assert(false);

							// TODO: skip what follows
						}
					}
				}

				NOLL_DEBUG("The source ");
				noll_debug_print_one_mark(mark_next_child);
				NOLL_DEBUG(" is NOT a PREFIX of the target ");
				noll_debug_print_one_mark(mark_i);
				NOLL_DEBUG("\n");

				// get the longest prefix
				noll_uid_array* lcp = noll_longest_common_prefix(mark_next_child, mark_i);
				assert(NULL != lcp);
				assert(!noll_vector_empty(lcp));

				NOLL_DEBUG("Their longest common prefix is ");
				noll_debug_print_one_mark(lcp);
				NOLL_DEBUG("\n");

				// TODO: this hack asserts that the node with the longest common
				// prefix is the source of the processed edge.
				// This should work for easier graphs, but will fail for more complex
				assert(noll_uid_array_equal(lcp, mark_i));
				noll_uid_array_delete(lcp);

				NOLL_DEBUG("Detected an s3() marker\n");

				// now, we create the corresponding symbol
				const noll_ta_symbol_t* leaf_symbol =
					noll_ta_symbol_get_unique_aliased_marking(3, mark_next_child);
				assert(NULL != leaf_symbol);

				NOLL_DEBUG("WARNING: inserting invalid states\n");

				// TODO: instead of getting a unique state, we might have only one
				// state for every used leaf symbol (such as it's done in Forester)
				size_t leaf_state = noll_get_unique();
				noll_uid_array_push(children, leaf_state);
				vata_add_transition(ta, leaf_state, leaf_symbol, NULL);
			}
		}

		assert(noll_vector_size(selectors) == noll_vector_size(children));

		NOLL_DEBUG("WARNING: ");
		NOLL_DEBUG(__func__);
		NOLL_DEBUG(": ignoring vars\n");

		const noll_ta_symbol_t* symbol = noll_ta_symbol_get_unique_allocated(
			selectors, vars, mark_i);
		assert(NULL != symbol);

		NOLL_DEBUG("Inserting transition q%lu -> %s", i, noll_ta_symbol_get_str(symbol));
		NOLL_DEBUG("(");
		for (size_t j = 0; j < noll_vector_size(children); ++j)
		{
			NOLL_DEBUG("q%u, ", noll_vector_at(children, j));
		}
		NOLL_DEBUG(")\n");

		NOLL_DEBUG("Adding transition over %s\n", noll_ta_symbol_get_str(symbol));

		vata_add_transition(ta, i, symbol, children);

		noll_uid_array_delete(children);
		noll_uid_array_delete(selectors);
		noll_uid_array_delete(vars);
	}

	NOLL_DEBUG("Starting traversing the edges\n");
	assert(NULL != g->mat);

	/* // the work stack that contains nodes to be processed */
	/* noll_uid_array* workstack = noll_uid_array_new(); */
	/* assert(NULL != workstack); */
	/* noll_uid_array_reserve(workstack, g->nodes_size); */
	/* noll_uid_array_push(workstack, initial_node); */
  /*  */
  /*  */
	/* noll_uid_array_delete(workstack); */

	const noll_uid_array* edges = g->mat[initial_node];
	assert(NULL != edges);

	for (size_t i = 0; i < noll_vector_size(edges); ++i)
	{
		const noll_edge_t* ed = noll_vector_at(g->edges, noll_vector_at(edges, i));
		assert(NULL != ed);
		NOLL_DEBUG("Edge from the initial node: %p\n", ed);
		assert(2 == noll_vector_size(ed->args));
		assert(noll_vector_at(ed->args, 0) == initial_node );
		NOLL_DEBUG("Neighbour of the initial node: %u\n", noll_vector_at(ed->args, 1));
	}












	noll_marking_list_delete(markings);

	for (size_t i = 0; i < noll_vector_size(g->edges); ++i) {
		NOLL_DEBUG("Processing edge (*g->edges)[%lu] = %p, ", i, noll_vector_at(g->edges, i));
		const noll_edge_t* edge = noll_vector_at(g->edges, i);
		assert(NULL != edge);
		NOLL_DEBUG("from = %u, to = %u, id = %u, kind = %u, label = %u, field name = %s\n",
			noll_vector_at(edge->args, 0),
			noll_vector_at(edge->args, 1),
			edge->id,
			edge->kind,
			edge->label,
			noll_field_name(edge->label));

		/* vata_symbol_t* symbol       = "symbol"; */
		/* assert(NOLL_EDGE_PTO == edge->kind); */
		/* assert(2 == noll_vector_size(edge->args)); */
		/* vata_state_t children[] = {noll_vector_at(edge->args, 1)}; */
		/* vata_add_transition(ta, noll_vector_at(edge->args, 0), symbol, children, 1); */
	}

	// TODO

	return ta;
}

