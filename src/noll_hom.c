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

#include "noll_hom.h"
#include "noll_entl.h"

NOLL_VECTOR_DEFINE (noll_shom_array, noll_shom_t*);

/* ====================================================================== */
/* Constructors/destructors */
/* ====================================================================== */

/* Allocate a homomorphism for the crt problem. */
noll_hom_t* 
noll_hom_alloc(void) {
	
	assert (noll_prob != NULL);
	
	noll_hom_t* h = (noll_hom_t*) malloc(sizeof(noll_hom_t));
	h->is_empty = false;
	h->shom = noll_shom_array_new();
	size_t sz = noll_vector_size(noll_prob->ngraph);
	assert (sz >= 1);
	noll_shom_array_reserve(h->shom, noll_vector_size(noll_prob->ngraph));
	
	return h;
}


/* ====================================================================== */
/* Getters/Setters */
/* ====================================================================== */

/* ====================================================================== */
/* Printers */
/* ====================================================================== */

void noll_hom_fprint(FILE* f, noll_hom_t* h) {
	assert(f != NULL);
	if (NULL == h)
	{
		// do sth
	}

	fprintf(f, "\nHom:[]\n");
}

/* ====================================================================== */
/* Solver */
/* ====================================================================== */


/**
 * Return the image of args by the mapping h of size size.
 */
noll_uid_array*
noll_hom_apply_size_array(uint_t* h, uint_t size, noll_uid_array* args) {
	noll_uid_array* res = noll_uid_array_new();
	noll_uid_array_reserve(res, noll_vector_size(args));
	for (uint_t i = 0; i < noll_vector_size(args); i++) {
		uint_t n1 = noll_vector_at(args,i);
		if (n1 >= size) {
			noll_uid_array_delete(res);
			res = NULL;
			goto hom_apply;
		}
		uint_t n2 = h[n1];
		noll_uid_array_push(res, n2);
	}
	hom_apply: return res;
}


/**
 * Given the graph g and the node of type node_ty which is included in term t,
 * fill (toFill=true) or intersect with (toFill=false) ptos (for points to)
 * and pred (for predicate) edges and add the edge id of beta to impl if
 * something is filled/accepted.
 */
void noll_graph_complete_edge(noll_graph_t* g, noll_uid_array* svar2edge,
		uint_t node, uint_t node_ty, noll_sterm_t* t, noll_edge_array* ptos,
		noll_edge_array* preds, noll_uid_array* impl, bool toFill) {

	if ((&g != &g) || (&node != &node) || (&node_ty != &node_ty) ||
		(&ptos != &ptos) || (&preds != &preds) || (&impl != &impl) ||
		(&toFill != &toFill))
	{
		assert(0);    // to avoid the "unused parameter" bug
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
void noll_graph_complete(noll_graph_t* g) {
	if (g->isComplete == true)
		return;
	if ((g->share == NULL) || (noll_vector_size(g->share) == 0)) {
		g->isComplete = true;
		return;
	}

	// Step1: build the mapping svar2edge: slocs -> edge
	noll_uid_array* svar2edge = noll_uid_array_new();
	noll_uid_array_reserve(svar2edge, noll_vector_size(g->svars));
	for (uint_t i = 0; i < noll_vector_size(g->svars); i++)
		noll_uid_array_push(svar2edge, UNDEFINED_ID);
	for (uint_t i = 0; i < noll_vector_size(g->edges); i++) {
		noll_edge_t* ei = noll_vector_at(g->edges,i);
		if ((ei->kind == NOLL_EDGE_PRED) && (ei->bound_svar != UNDEFINED_ID))
			noll_vector_at(svar2edge,ei->bound_svar) = i;
	}

	// Step2: go through the sharing constraints
	// TODO: it works only if the set of sharing constraints is minimum
	for (uint_t i = 0; i < noll_vector_size(g->share); i++) {
		noll_atom_share_t* s = noll_vector_at(g->share,i);
		if ((s->kind == NOLL_SHARE_NI) || (s->kind > NOLL_SHARE_SUBSET))
			continue;
		// declare the node and the type that will be constrained by the constraint
		uint_t node = UNDEFINED_ID;
		uint_t node_ty = UNDEFINED_ID;
		if (s->kind == NOLL_SHARE_IN) {
			assert (s->t_left != NULL);
			assert (s->t_left->lvar < noll_vector_size(g->lvars));
			// constrain node in U beta_i
			node = g->var2node[s->t_left->lvar];
			node_ty = noll_var_record(g->lvars, s->t_left->lvar);
		} else {
			assert (s->kind == NOLL_SHARE_SUBSET);
			assert (s->t_left->svar < noll_vector_size(g->svars));
			// constraint alpha <= U beta_i
			// get the index of alpha and the projection type, if any
			uint_t alpha = s->t_left->svar;
			uint_t alpha_ty = (s->t_left->lvar == UNDEFINED_ID) ? UNDEFINED_ID
					: noll_var_record(g->lvars, s->t_left->lvar);
			// get the edge bound to alpha
			uint_t alpha_ei = noll_vector_at(svar2edge, alpha);
			if (alpha_ei == UNDEFINED_ID) // no edge bound
				continue;
			noll_edge_t* alpha_e = noll_vector_at(g->edges,alpha_ei);
			uint_t alpha_pid = alpha_e->label;
			if (alpha_e->impl != NULL && noll_vector_size(alpha_e->impl) >= 1)
				// implicit edge, nothing to do
				continue;
			// get the source of this edge
			node = noll_vector_at(alpha_e->args,0);
			// get the type of the node start of alpha = type of the predicate
			const noll_pred_t* pred = noll_pred_getpred(alpha_pid);
			assert(NULL != pred);
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
		assert (noll_vector_size(s->t_right) > 0);
		noll_edge_array* ptos = noll_edge_array_new();
		noll_edge_array* preds = noll_edge_array_new();
		noll_uid_array* impl = noll_uid_array_new();
		// TODO: fills ptos ands preds with constraints
		noll_graph_complete_edge(g, svar2edge, node, node_ty,
				noll_vector_at(s->t_right,0), ptos, preds, impl, true); // fill
		// intersect ptos and preds with the others members of the unions
		// if they include type node_ty
		for (uint_t i = 1; i < noll_vector_size(s->t_right); i++) {
			noll_graph_complete_edge(g, svar2edge, node, node_ty,
					noll_vector_at(s->t_right,i), ptos, preds, impl, false); // intersect
		}
		// TODO
		//      if ptos != emptyset then
		//         add edge pto and say that it is implicit from U beta_i
		//      if preds != emptyset then
		//         add edge pred and say that it is implicit from U beta_i
		//         add a new svar and bound it to pred
		//         add constraint svar <= U beta_i
		if (noll_vector_size(s->t_right) == 1) {
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
int noll_graph_get_edge_form(noll_graph_t* g, noll_space_t* form,
		noll_uid_array* mapvar, noll_uid_array* res) {

	assert (g != NULL);
	assert (form != NULL);
	assert (mapvar != NULL);
	assert (res != NULL);

	switch (form->kind) {
	case NOLL_SPACE_EMP:
		// nothing to do
		return 1;
	case NOLL_SPACE_PTO: {
		// node on which is mapped the source var
		assert (form->m.pto.sid < noll_vector_size(mapvar));
		uint_t nsrc = noll_vector_at(mapvar,form->m.pto.sid);
#ifndef NDEBUG
		printf("%s\n", noll_vector_at(g->lvars,nsrc)->vname);
		printf("%s\n", noll_vector_at(g->lvars,form->m.pto.sid)->vname);
#endif
		// search in g the same fields from nsrc
		if (g->mat[nsrc] != NULL) {
			noll_uid_array* tmp_res = noll_uid_array_new(); // temporary array of edges
			for (uint_t i = 0; i < noll_vector_size(form->m.pto.fields); i++) {
				uint_t fid = noll_vector_at(form->m.pto.fields,i);
				// search the pto edge in g
				bool found = false;
				for (uint_t j = 0; j < noll_vector_size(g->mat[nsrc]) && !found; j++) {
					uint_t ej = noll_vector_at(g->mat[nsrc],j);
					noll_edge_t* edge_j = noll_vector_at(g->edges,ej);
					if ((edge_j->kind == NOLL_EDGE_PTO) && (edge_j->label
							== fid)) {
						// ok, it matched
						found = true;
						// push the field first
						noll_uid_array_push(tmp_res, ej);
						// verify/update mapping of variables
						uint_t vdst = noll_vector_at(form->m.pto.dest,i);
						if (noll_vector_at(mapvar,vdst) == UNDEFINED_ID)
							noll_vector_at(mapvar,vdst)
									= noll_vector_at(edge_j->args,1);
						assert (noll_vector_at(mapvar,vdst) == noll_vector_at(edge_j->args,1));
					}
				}
				if (!found) {
					// no match for this edge
					fprintf(
							stdout,
							"Edge mapping fails: g2 edge from node %d for field %d!\n",
							nsrc, fid);
					fflush(stdout);
					noll_uid_array_delete(tmp_res);
					// TODO: shall also remove mapping from mapvar!
					return 0;
				}
			}
			// move edges to result
			for (uint_t i = 0; i < noll_vector_size(tmp_res); i++)
				noll_uid_array_push(res, noll_vector_at(tmp_res,i));
			noll_uid_array_delete(tmp_res);
		} else {
			fprintf(stdout,
					"Edge mapping fails: g2 points-to edge from node %d!\n",
					nsrc);
			fflush(stdout);
			return 0;
		}
		break;
	}
	case NOLL_SPACE_LS: {
		// Search edge labeled by form->label and some arguments mapped like mapvar
		uint_t pid = form->m.ls.pid;
		// build the array of node arguments
		uint_t farg = UNDEFINED_ID; // first arg mapped to a node
		noll_uid_array* nargs = noll_uid_array_new();
		for (uint_t i = 0; i < noll_vector_size(form->m.ls.args); i++) {
			uint_t vi = noll_vector_at(form->m.ls.args,i);
			uint_t ni = noll_vector_at(mapvar,vi);
			noll_uid_array_push(nargs, ni);
			if (ni != UNDEFINED_ID && farg == UNDEFINED_ID)
				farg = ni;
		}
		if (farg == UNDEFINED_ID) {
			// very big choice of mappings in g, signal it
#ifndef NDEBUG
			fprintf (stdout, "Edge mapping: too much choices for edge with predicate %d!", pid);
			fflush(stdout);
#endif
		}
		// search edge in g with same arguments
		uint_t found_ei = UNDEFINED_ID;
		for (uint_t ei = 0; (ei < noll_vector_size(g->edges)) && (found_ei
				== UNDEFINED_ID); ei++) {
			noll_edge_t* edge_i = noll_vector_at(g->edges, ei);
			if (edge_i->kind == NOLL_EDGE_PRED && edge_i->label == pid) {
				// same predicate, verify args
				bool same = true;
				for (uint_t i = 0; i < noll_vector_size(edge_i->args) && same; i++)
					if ((noll_vector_at(nargs,i) != UNDEFINED_ID)
							&& (noll_vector_at(nargs,i)
									!= noll_vector_at(edge_i->args,i)))
						same = false;
				if (same) {
					// push ei in result
					found_ei = ei;
#ifndef NDEBUG
					fprintf (stdout, "Edge mapping: g2 edge %d mapped to formula!\n", ei);
					fflush(stdout);
#endif
					noll_uid_array_push(res, ei);
					// update mapvar
					for (uint_t i = 0; i < noll_vector_size(edge_i->args)
							&& same; i++)
						if (noll_vector_at(nargs,i) == UNDEFINED_ID) {
							uint_t vi = noll_vector_at(form->m.ls.args,i);
							noll_vector_at(mapvar,vi)
									= noll_vector_at(edge_i->args,i);
						}
				}
			}
		}
		noll_uid_array_delete(nargs);
		if (found_ei == UNDEFINED_ID) {
			fprintf(stdout, "Edge mapping fails: g2 edge with predicate %d!\n",
					pid);
			fflush(stdout);
			return 0;
		}
		break;
	}
	case NOLL_SPACE_SSEP: {
		// TODO: break as soon as not matching
		noll_uid_array** tres = (noll_uid_array**) malloc(
				noll_vector_size(form->m.sep) * sizeof(noll_uid_array*));
		uint_t i = 0;
		for (; i < noll_vector_size(form->m.sep); i++) {
			tres[i] = noll_uid_array_new();
			int r = noll_graph_get_edge_form(g, noll_vector_at(form->m.sep, i),
					mapvar, tres[i]);
			if (r == 0)
				break;
		}
		if (i == noll_vector_size(form->m.sep)) {
			// success,
			// TODO: verify separation
			// push edges to res
			for (; i < noll_vector_size(form->m.sep); i++) {
				for (uint_t j = 0; j < noll_vector_size(tres[i]); j++) {
					noll_uid_array_push(res, noll_vector_at(tres[i], j));
				}
				noll_uid_array_delete(tres[i]);
			}
			free(tres);
		} else
			return 0;
		break;
	}
	case NOLL_SPACE_WSEP:
#ifndef NDEBUG
		fprintf (stdout, "NYI: wsep formula for predicate definition!\n");
		fflush(stdout);
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
void noll_graph_get_edge_path(noll_graph_t* g, noll_edge_e kind, uint_t label,
		noll_uid_array* args, noll_uid_array* res) {

	// store of edge identifiers matching the searched edge in this function
	noll_uid_array* temp_res = noll_uid_array_new();
	uint_t uint_temp = noll_vector_size(temp_res);
	// array used to store the new arguments when searching a path
	// from a new source node
	noll_uid_array* args0 = noll_uid_array_new();
	// source and destination nodes for edge searched
	uint_t nsrc = noll_vector_at(args,0);
	uint_t ndst = noll_vector_at(args,1);
	// a new intermediary node
	uint_t nend = UNDEFINED_ID;

#ifndef NDEBUG
	fprintf (stdout, "---- Search path for edge n%d---(kind=%d, label=%d)-->n%d:\n",
			nsrc, kind, label, ndst);
#endif

	if (g->mat[nsrc] != NULL) {
		for (uint_t i = 0; i < noll_vector_size(g->mat[nsrc]); i++) {
			uint_t ei = noll_vector_at(g->mat[nsrc],i);
			noll_edge_t* edge_i = noll_vector_at(g->edges,ei);
			if ((edge_i->kind == kind) && (edge_i->label == label)
					&& (noll_vector_size(edge_i->args)
							== noll_vector_size(args))) {
#ifndef NDEBUG
				fprintf (stdout, "\t found e%d, same kind and label\n", ei);
#endif
				// edge found with the same kind, label and args size,
				// check the other arguments than source and destination nodes are equal
				bool ishom = true;
				for (uint_t j = 2; j < noll_vector_size(args)
						&& (ishom == true); j++)
					if (noll_vector_at(args,j)
							!= noll_vector_at(edge_i->args,j)) {
#ifndef NDEBUG
						fprintf (stdout, "\t\t but different arg %d (n%d != n%d)\n",
								j, noll_vector_at(args,j), noll_vector_at(edge_i->args,j));
#endif
						ishom = false;
					}
				if (ishom == true) {
#ifndef NDEBUG
					fprintf (stdout, "\t\t and same args\n");
#endif
					noll_uid_array_push(temp_res, ei);
					nend = noll_vector_at(edge_i->args,1); // destination of the edge
				}
			}
		}
	}

	uint_temp = noll_vector_size(temp_res);
#ifndef NDEBUG
	fprintf (stdout, "\t %d edges matches!\n", uint_temp);
#endif

	// The positive case: edge match and destination nodes match
	// both kind of edges
	if ((uint_temp > 0) && (nend == ndst)) {
		// an edge has been found and the destination node is the same
		// move from temp_res to res
		goto path_ok;
	}

	// The negative case: for PTO edge, either no edge found
	// OR pto edge found but not the good destination node
	if ((kind == NOLL_EDGE_PTO) && ((uint_temp == 0)
			|| ((noll_vector_size(temp_res) > 0) && (nend != ndst)))) {
		// nothing to be done
		goto path_nok;
	}

	assert (kind == NOLL_EDGE_PRED);
	// The negative case: for PRED edge, no edge found
	if (uint_temp == 0) {
		// try to match predicate definition
		const noll_pred_t* p = noll_pred_getpred(label);
		assert(NULL != p);
		// init mapping of variables to nodes for this definition, UNDEFINED_ID if not known
		noll_uid_array* mapvar = noll_uid_array_new();
		for (uint_t i = 0; i < noll_vector_size(p->def->vars); i++)
			noll_uid_array_push(mapvar, UNDEFINED_ID);
		// TODO: correct?
		for (uint_t i = 0; i < noll_vector_size(args); i++)
			noll_vector_at(mapvar,i) = noll_vector_at(args,i);
		// match sigma_0 of the predicate
		noll_graph_get_edge_form(g, p->def->sigma_0, mapvar, temp_res);
		// this call will return at least one edge if found one
		uint_temp = noll_vector_size(temp_res);
		if (uint_temp == 0)
			goto path_nok;
		// if succeed try also sigma_1 from nsrc if not null
		if (p->def->sigma_1 != NULL) {
			noll_uid_array* temp_res1 = noll_uid_array_new();
			noll_graph_get_edge_form(g, p->def->sigma_1, mapvar, temp_res1);
			if (noll_vector_size(temp_res1) == 0) {
				// error
				noll_uid_array_delete(temp_res1);
				goto path_nok;
			}
			// else, push the result in temp_res
			uint_temp = noll_vector_size(temp_res);
		}
		// the predicate succeed on nsrc,
		// see if there is another intermediate node, look at first edge recorded
		uint_t forward_e = noll_vector_at(temp_res,0);
		nend = noll_vector_at(noll_vector_at(g->edges, forward_e)->args,1);
		if (nend == ndst) {
			// no intermediate node, push the result in res
			goto path_ok;
		}
		// there is an intermediate node,
		// continue with the positive case above
	}

	// The positive case: there is a predicate edge or match
	// try this function again with nend as initial node
	// TODO: transform it in a loop
	noll_uid_array_copy(args0, args);
	noll_vector_at(args0, 0) = nend;
	noll_graph_get_edge_path(g, kind, label, args0, temp_res);
	// if it worked, then push the edges in res
	if (noll_vector_size(temp_res) > uint_temp) {
		path_ok:
#ifndef NDEBUG
		fprintf (stdout, "=== path found-size%d: [", uint_temp);
#endif
		for (uint_t i = 0; i < noll_vector_size(temp_res); i++) {
			noll_uid_array_push(res, noll_vector_at(temp_res,i));
#ifndef NDEBUG
			fprintf (stdout, "%d,", i);
#endif
		}
#ifndef NDEBUG
		fprintf (stdout, "]\n");
#endif
	}

	path_nok: noll_uid_array_delete(args0);
	noll_uid_array_delete(temp_res);
	return;
}



/**
 * Return the edges of g which can represent an edge
 * of kind between nodes in args and label l.
 */
noll_uid_array*
noll_graph_get_edge(noll_graph_t* g, noll_edge_e kind, noll_uid_array* args,
		uint_t label) {
	assert (g != NULL);
	assert (args != NULL);
	assert (noll_vector_size(args) >= 2);
	assert (kind == NOLL_EDGE_PTO || kind == NOLL_EDGE_PRED);

	noll_uid_array* res = noll_uid_array_new();

	// First try: search a path from nsrc with this label
	noll_graph_get_edge_path(g, kind, label, args, res);
	if (noll_vector_size(res) > 0)
		return res;

	// If not such edge is found, two choices:
	// A) need to saturate, and thus change constraints in g (for pto and ls edges)
	// B) there is a path, not a single edge (for ls edges)
	// The order of dealing A followed by B, but some times only B is needed
	if ((noll_vector_size(res) == 0) && (g->isComplete == false)) {
		noll_graph_complete(g); // A: saturation only fill implicit constraints
		// This can be done incrementally, only to cover this edge or fully
	}

	// B: second try, search the path
	noll_graph_get_edge_path(g, kind, label, args, res);

	// if saturation gives nothing, return NULL
	if (noll_vector_size(res) == 0) {
		noll_uid_array_delete(res);
		res = NULL;
	}

	return res;
}

/**
 * Return 1 if the edge e has been already mapped by used,
 * otherwise 0.
 */
int noll_graph_used(noll_uid_array* used, uint_t e, noll_graph_t* g) {
	assert (used != NULL);
	assert (e < noll_vector_size(used));

	if (&g != &g)
	{
		assert(0);
	}

	// directly used
	if (noll_vector_at(used,e) != UNDEFINED_ID)
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

int ***noll_graph_paths_fields(noll_graph_t* g, noll_uid_array* edge_set) {

	bool *in_set = (bool*) malloc(noll_vector_size(g->edges) * sizeof(bool));
	for (uint_t i = 0; i < noll_vector_size(g->edges); i++) {
		in_set[i] = false;
	}
	for (uint_t i = 0; i < noll_vector_size(edge_set); i++)
		in_set[noll_vector_at(edge_set,i)] = true;

	int ***paths = (int***) malloc(noll_vector_size(fields_array)
			* sizeof(int**));
	for (uint_t i = 0; i < noll_vector_size(fields_array); i++) {
		paths[i] = (int**) malloc(g->nodes_size * sizeof(int*));
		for (uint_t j = 0; j < g->nodes_size; j++) {
			paths[i][j] = (int*) malloc(g->nodes_size * sizeof(int));
			for (uint_t k = 0; k < g->nodes_size; k++)
				paths[i][j][k] = 0;
		}
	}
	for (uint_t ei = 0; ei < noll_vector_size(g->edges); ei++) {
		noll_edge_t* e = noll_vector_at(g->edges,ei);
		uint_t label = e->label;
		uint_t src = noll_vector_at(e->args,0);
		uint_t dst = noll_vector_at(e->args,1);

		if (e->kind == NOLL_EDGE_PTO) {
			paths[label][src][dst] = in_set[ei] ? 2 : 1;

			for (uint_t ni = 0; ni < g->nodes_size; ni++)
				if (paths[label][ni][src]) {
					paths[label][ni][dst] = ((paths[label][ni][src] == 2)
							&& in_set[ei]) ? 2 : 1;
				}
		} else if (e->kind == NOLL_EDGE_PRED) {
			const noll_pred_t* pred = noll_pred_getpred(label);
			assert(NULL != pred);
			noll_uid_array* fields0 = pred->typ->pfields0;
			for (uint_t fi = 0; fi < noll_vector_size(fields0); fi++) {
				uint_t f = noll_vector_at(fields0,fi);
				paths[f][src][dst] = in_set[ei] ? 2 : 1;
				for (uint_t ni = 0; ni < g->nodes_size; ni++)
					if (paths[label][ni][src]) {
						paths[label][ni][dst] = ((paths[label][ni][src] == 2)
								&& in_set[ei]) ? 2 : 1;
					}

			}
		} else {
#ifndef NDEBUG
			printf("Edge type not considered\n");
#endif
		}

	}

	bool cont = true;
	while (cont) {
		cont = false;
		for (uint_t i = 0; i < noll_vector_size(fields_array); i++)
			for (uint_t j = 0; j < g->nodes_size; j++)
				for (uint_t k = 0; k < g->nodes_size; k++)
					for (uint_t t = 0; t < g->nodes_size; t++)
						if (paths[i][j][k] && paths[i][k][t]) {
							int temp = (paths[i][j][k] == 2 && paths[i][k][t]
									== 2) ? 2 : 1;
							if (temp != paths[i][j][t])
								cont = true;
							paths[i][j][t] = temp;
						}

	}

#ifndef NDEBUG
	for(uint_t i=0;i< noll_vector_size(fields_array);i++) {
		for(uint_t j=0;j< g->nodes_size;j++) {
			for(uint_t k=0;k<g->nodes_size;k++)
			if(paths[i][j][k])
			printf("Between n%d and n%d there is an %s-path=%d\n",j,k,noll_vector_at(fields_array,i)->name,paths[i][j][k]);
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

bool **noll_graph_field_defined(noll_graph_t *g, int ***paths) {
	bool **res = (bool**) malloc(g->nodes_size * sizeof(bool*));
	for (uint_t i = 0; i < g->nodes_size; i++) {
		res[i] = (bool*) malloc(noll_vector_size(fields_array) * sizeof(bool));
		for (uint_t j = 0; j < noll_vector_size(fields_array); j++)
			res[i][j] = false;
	}

	// for any points-to edge labeled by f and starting in src, f is defined in src and any node from
	// which there exists an f-path to src
	for (uint_t i = 0; i < noll_vector_size(g->edges); i++) {
		noll_edge_t* e = noll_vector_at(g->edges,i);
		if (e->kind == NOLL_EDGE_PTO) {
			uint_t f = e->label;
			uint_t src = noll_vector_at(e->args,0);
			res[src][f] = true;
#ifndef NDEBUG
			printf("Field %s defined in n%d\n",noll_vector_at(fields_array,f)->name,src);
#endif
			for (uint_t i = 0; i < g->nodes_size; i++)
				if (paths[f][i][src]) {
					res[i][f] = true;
#ifndef NDEBUG
					printf("Field %s defined in n%d\n",noll_vector_at(fields_array,f)->name,i);
#endif
				}
		}
	}

	// for any disequality edge (i,j),
	// 			if there exists an f-path between i and j then f is defined in i
	//			if there exists a node k s.t. there exists an f-path between k and i and an f-path between k and j
	//					then f is defined in k
	for (uint_t i = 0; i < g->nodes_size; i++)
		for (int j = i - 1; j >= 0; j--) {
			bool diff = g->diff[i][j];
			for (uint_t f = 0; f < noll_vector_size(fields_array); f++) {
				if (diff & paths[f][i][j]) {
					res[i][f] = true;
#ifndef NDEBUG
					printf("Field %s defined in n%d\n",noll_vector_at(fields_array,f)->name,i);
#endif
				}
				for (uint_t k = 0; k < g->nodes_size; k++) {
					if (paths[f][k][i] && paths[f][k][j]) {
						res[k][f] = true;
#ifndef NDEBUG
						printf("Field %s defined in n%d\n",noll_vector_at(fields_array,f)->name,k);
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
int noll_graph_check_acyclicity(noll_graph_t* g, noll_uid_array* edge_set) {
#ifndef NDEBUG
	printf("===Call to acyclic\n");
#endif
	int ***paths = noll_graph_paths_fields(g, edge_set);
	bool **def_fields = noll_graph_field_defined(g, paths);
	for (uint_t i = 0; i < noll_vector_size(edge_set); i++)
		for (uint_t j = i + 1; j < noll_vector_size(edge_set); j++) {
			noll_edge_t* e1 =
					noll_vector_at(g->edges,noll_vector_at(edge_set,i));
			noll_edge_t* e2 =
					noll_vector_at(g->edges,noll_vector_at(edge_set,j));
			uint_t dest1 = noll_vector_at(e1->args,1);
			uint_t dest2 = noll_vector_at(e2->args,1);
			bool isdiff = (dest1 < dest2) ? g->diff[dest2][dest1]
					: g->diff[dest1][dest2];
			// if the destinations of the two edges are not equal it is ok
			if (isdiff)
				continue;

			// otherwise, check if there exists some f-path between the destinations of the
			// two edges such that f is surely defined in the destination of the second edge
			bool disapear = false;
			for (uint_t f = 0; f < noll_vector_size(fields_array); f++)
				if (paths[f][dest1][dest2] == 2 && def_fields[dest2][f]) {
					disapear = true;
					break;
				}
			if (disapear)
				continue;
#ifndef NDEBUG
			printf("===Return from acyclic 0\n");
#endif
			return 0;
		}
#ifndef NDEBUG
	printf("===Return from acyclic 1\n");
#endif
	return 1;
}

/**
 * Search a homomorphism to prove noll_prob.
 * Store the homomorphism found in noll_prob->hom.
 */
int noll_graph_shom(noll_hom_t* h, size_t i);
int noll_graph_homomorphism(void) {

	assert (noll_prob != NULL);
	
	/* allocate the homomorphism */
	noll_hom_t* h = noll_hom_alloc();
	
	/* compute a simple homomorphism for each negative graph */
	/* TODO: update with the algo for disjunctions */
	int res = 1;
	for (size_t i = 0; i < noll_vector_size(noll_prob->ngraph); i++) {
		res = noll_graph_shom(h, i);
		if (res == 0) {
			break;
		}
	}
	noll_prob->hom = h;
	return res;
}

int 
noll_graph_shom(noll_hom_t* hs, size_t i) {
	
	assert (hs != NULL);
	
    /* Only to make the code to compile */
	noll_graph_t* g1 = noll_vector_at(noll_prob->ngraph,i);
	noll_graph_t* g2 = noll_prob->pgraph;
	

	int res = 1;
	uint_t* h = NULL; // for homomorphism,
	// h[node id in g1] = node id in g2
	noll_uid_array* used = NULL; // for used set,
	// used[edge id in g2] = edge id in g1
	noll_uid_array** h_edge = NULL; // for edge mapping,
	// h_edge[edge id in g1] = edge ids in g2

	/* Graphs are not empty! */
	assert(g1 != NULL);
	assert(g1->var2node != NULL);
	assert(g1->edges != NULL);
	assert(g2 != NULL);
	assert(g2->var2node != NULL);
	assert(g2->edges != NULL);

	/*
	 * Map all nodes in g1 to nodes in g2 such that labeling is respected
	 */
	h = (uint_t*) malloc(g1->nodes_size * sizeof(uint_t));
	// initialize entries by default
	for (uint_t i = 0; i < g1->nodes_size; i++)
		h[i] = UNDEFINED_ID;
	for (uint_t v = 0; v < noll_vector_size(g1->lvars); v++) {
		// TODO: incorrect now with local vars, check the name of the variable
		uint_t n1v = g1->var2node[v];
		uint_t n2v = g2->var2node[v];
		if (n1v != UNDEFINED_ID) {
			if (n2v != UNDEFINED_ID)
				h[n1v] = n2v;
			else {
				res = 0;
				goto check_hom;
			}
		}
	}
	// verify that no default value is still in h
	// TODO: what happens with nodes labeled by local vars?
	for (uint_t i = 0; i < g1->nodes_size; i++)
		if (h[i] == UNDEFINED_ID) {
			res = 0;
			fprintf(stdout, "Node n%d of right side graph not mapped!", i);
			goto check_hom;
		}

#ifndef NDEBUG
	fprintf (stdout, "Homomorphism built from the labeling with program variables:\n\t[");
	for (uint_t i = 0; i < g1->nodes_size; i++)
	fprintf(stdout, "n%d --> n%d,", i, h[i]);
	fprintf (stdout, "]\n");
#endif

	/*
	 * Verify difference edges from g1 mapped to diff edges in g2
	 */
	for (uint_t ni1 = 1; ni1 < g1->nodes_size; ni1++)
		for (uint_t nj1 = 0; nj1 < ni1; nj1++)
			if (g1->diff[ni1][nj1]) {
				uint_t ni2 = h[ni1];
				uint_t nj2 = h[nj1];
				bool isdiff2 = (ni2 < nj2) ? g2->diff[nj2][ni2]
						: g2->diff[ni2][nj2];
				if (isdiff2 == false) {
					res = 0;
					// TODO: put message with program variables
					fprintf(
							stdout,
							"Difference edge (n%d != n%d) in right side graph ",
							ni1, nj1);
					fprintf(
							stdout,
							"is not mapped to (n%d != n%d) in left side graph!",
							ni2, nj2);
					goto check_hom;
				}
			}

	// used set, used[ei2 in g2] = ei1 in g1
	// ei2 from g2 is used to map ei1
	// (several edges in g2 are needed for list segments)
	used = noll_uid_array_new();
	noll_uid_array_reserve(used, noll_vector_size(g2->edges));
	for (uint_t ei2 = 0; ei2 < noll_vector_size(g2->edges); ei2++) {
		noll_uid_array_push(used, UNDEFINED_ID);
	}

	// edge mapping, h_edge[ei1 in g1] = array of edge ids in g2
	h_edge = (noll_uid_array**) malloc(noll_vector_size(g1->edges)
			* sizeof(noll_uid_array*));
	for (uint_t ei1 = 0; ei1 < noll_vector_size(g1->edges); ei1++) {
		h_edge[ei1] = noll_uid_array_new();
	}
	/*
	 * Verify that edges in g1 may be mapped to (implicit) pto edges in g2
	 */
	for (uint_t ei1 = 0; ei1 < noll_vector_size(g1->edges); ei1++) {
#ifndef NDEBUG
		fprintf(stdout, "==== Mapping edge %d in g1: \n", ei1);
#endif
		noll_edge_t* edge_i1 = noll_vector_at(g1->edges,ei1);
		// apply the h on the args of this edge
		noll_uid_array* args2 = noll_hom_apply_size_array(h, g1->nodes_size,
				edge_i1->args);
		// search the mapping of ei1 into a (list of) edge(s),
		// by, if needed, saturating g2
		noll_uid_array* lei2 = noll_graph_get_edge(g2, edge_i1->kind, args2,
				edge_i1->label);

		// if edges has been added in g2, update used
		for (uint_t i = noll_vector_size(used); i < noll_vector_size(g2->edges); i++)
			noll_uid_array_push(used, UNDEFINED_ID);
		if (lei2 != NULL) {
#ifndef NDEBUG
			fprintf (stdout, "---- right edge-%d mapped to left edges-[", ei1);
#endif
			for (uint_t i2 = 0; i2 < noll_vector_size(lei2); i2++) {
				uint_t ei2 = noll_vector_at(lei2,i2);
#ifndef NDEBUG
				fprintf (stdout, "%d,", ei2);
#endif
				if (noll_graph_used(used, ei2, g2)) {
					res = 0;
					fprintf(stdout, "Edge (left) %d is already used!", ei2);
					goto check_hom;
				}
				noll_vector_at(used,ei2) = ei1;
				noll_uid_array_push(h_edge[ei1], ei2);
			}
#ifndef NDEBUG
			fprintf (stdout, "]\n");
#endif
		} else {
			res = 0;
			fprintf(stdout, "---- right edge %d not mapped!", ei1);
			goto check_hom;
		}

		//if g1 is precise, we need to check that the set of edges lei2 is acyclic
		if (g1->is_precise && (lei2 != NULL))
			if (!noll_graph_check_acyclicity(g2, lei2)) {
				fprintf(
						stdout,
						"=== right edge-%d mapped to a set of edges that may contain a cycle\n",
						ei1);
				res = 0;
				goto check_hom;
			}
	}

	// if g1 is precise check that all edges in g2 are used
	for (uint_t i = 0; i < noll_vector_size(used); i++)
		if (noll_vector_at(used,i) == UNDEFINED_ID) {
			res = 0;
			fprintf(stdout, "Edge (left) %d not used!", i);
			goto check_hom;
		}

	/*
	 * Verify that the separation constraints are satisfied by the edge mapping, i.e.,
	 * for any edge e1i in g1 strong separated from e1j then
	 *     h_edge[e1i] are all strong separated from h_edge[e1j]
	 */
	for (uint_t ei1 = 0; ei1 < noll_vector_size(g1->edges); ei1++) {
		// the edge in g1
		noll_edge_t* edge_i1 = noll_vector_at(g1->edges,ei1);
		// the mapped edges in g2
		noll_uid_array* lei2 = h_edge[ei1];
		assert (lei2 != NULL);
		assert (noll_vector_size(lei2) >= 1);
		// go through the separated edges from ei1 in g1
		for (uint_t j1 = 0; j1 < noll_vector_size (edge_i1->ssep); j1++) {
			uint_t ej1 = noll_vector_at(edge_i1->ssep,j1);
			// ej1 is mapped to edges in g2
			noll_uid_array* lej2 = h_edge[ej1];
			assert (lej2 != NULL);
			assert (noll_vector_size(lej2) >= 1);
			// TODO: improve complexity here by sorting the arrays of ssep
			// for each edge in lei2, check that its separation set includes lej2
			for (uint_t i2 = 0; i2 < noll_vector_size(lei2); i2++) {
				uint_t ei2 = noll_vector_at(lei2,i2);
				noll_uid_array* ssepi2 = noll_vector_at(g2->edges,ei2)->ssep;
				for (uint_t j2 = 0; j2 < noll_vector_size(lej2); j2++) {
					uint_t ej2 = noll_vector_at(lej2,j2);
					bool found = false;
					for (uint_t si2 = 0; si2 < noll_vector_size(ssepi2)
							&& !found; si2++) {
						uint_t sei2 = noll_vector_at(ssepi2,si2);
						if (ej2 == sei2)
							found = true;
					}
					if (!found) {
						res = 0;
						fprintf(stdout,
								"Mapping of edges (right) %d --> (left) %d",
								ei1, ei2);
						fprintf(
								stdout,
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
	if (h_edge != NULL) {
		for (uint_t ei1 = 0; ei1 < noll_vector_size(g1->edges); ei1++) {
			noll_edge_t* e1 = noll_vector_at(g1->edges,ei1);
			noll_sterm_t* sterm_e1 = NULL; // term built for this edge
			if (e1->kind == NOLL_EDGE_PRED) {
				// get its set variable
				uint_t svar_e1 = e1->bound_svar;
				sterm_e1 = noll_sterm_new_var(svar_e1, NOLL_STERM_SVAR);
			} else if (e1->kind == NOLL_EDGE_PTO) {
				// get its location variable (node)
				uint_t node_e1 = noll_vector_at(e1->args,0);
				uint_t var_e1 = noll_graph_get_var(g1, node_e1);
				sterm_e1 = noll_sterm_new_var(var_e1, NOLL_STERM_LVAR);
			} else
				assert(0);
			// build the term from h_edge[e1]
			noll_sterm_array* sterm_h_e1 = noll_sterm_array_new();
			for (uint_t ei2 = 0; ei2 < noll_vector_size(h_edge[ei1]); ei2++) {
				noll_edge_t* e2 = noll_vector_at(g2->edges,ei2);
				noll_sterm_t* sterm_e2 = NULL;
				if (e2->kind == NOLL_EDGE_PRED)
					sterm_e2 = noll_sterm_new_var(e2->bound_svar,
							NOLL_STERM_SVAR);
				else if (e2->kind == NOLL_EDGE_PTO)
					sterm_e2 = noll_sterm_new_var(noll_vector_at(e2->args,0),
							NOLL_STERM_LVAR);
				else
					assert(0);
				// push constraint sterm_e2 <= sterm_e1
				noll_atom_share_t* e2_in_e1 = (noll_atom_share_t*) malloc(
						sizeof(noll_atom_share_t));
				e2_in_e1->kind = NOLL_SHARE_SUBSET;
				e2_in_e1->t_left = noll_sterm_copy(sterm_e2);
				e2_in_e1->t_right = noll_sterm_array_new();
				noll_sterm_array_push(e2_in_e1->t_right, noll_sterm_copy(
						sterm_e1));
				noll_share_array_push(g2->share, e2_in_e1);
				// push term sterm_e2 in sterm_h_e1
				noll_sterm_array_push(sterm_h_e1, sterm_e2);
			}
			// push constraint sterm_e1 <= sterm_h_e1
			noll_atom_share_t* e1_in_h_e1 = (noll_atom_share_t*) malloc(
					sizeof(noll_atom_share_t));
			e1_in_h_e1->kind = NOLL_SHARE_SUBSET;
			e1_in_h_e1->t_left = sterm_e1;
			e1_in_h_e1->t_right = sterm_h_e1;
			noll_share_array_push(g2->share, e1_in_h_e1);
		}
	}

	check_hom: if (h != NULL)
		free(h);
	if (used != NULL) {
		noll_uid_array_delete(used);
	}
	if (h_edge != NULL) {
		for (uint_t ei1 = 0; ei1 < noll_vector_size(g1->edges); ei1++) {
			noll_uid_array_delete(h_edge[ei1]);
		}
		free(h_edge);
	}
	return res;
}
