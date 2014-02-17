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
 * Graph representation of NOLL formulas.
 */

#include "noll_types.h"
#include "noll_form.h"
#include "noll_graph.h"

NOLL_VECTOR_DEFINE (noll_edge_array, noll_edge_t*)
;

NOLL_VECTOR_DEFINE (noll_graph_array, noll_graph_t*)
;

/* ====================================================================== */
/* Constructors/destructors */
/* ====================================================================== */

noll_edge_t*
noll_edge_alloc(noll_edge_e kind, uint_t src, uint_t dst, uint_t label) {
	noll_edge_t* e = (noll_edge_t*) malloc(sizeof(noll_edge_t));
	e->kind = kind;
	e->label = label;
	e->args = noll_uid_array_new();
	noll_uid_array_push(e->args, src);
	noll_uid_array_push(e->args, dst);
	e->id = UNDEFINED_ID;
	e->bound_svar = UNDEFINED_ID;
	; // index of the set variable in slocs_array bounded to the edge, or UNDEFINED_ID
	e->impl = NULL;
	e->ssep = noll_uid_array_new();
	return e;
}

void noll_edge_free(noll_edge_t* e) {
	if (e == NULL)
		return;
	if (e->args != NULL) {
		noll_uid_array_delete(e->args);
		e->args = NULL;
	}
	if (e->impl != NULL) {
		noll_uid_array_delete(e->impl);
		e->impl = NULL;
	}
	if (e->ssep != NULL) {
		noll_uid_array_delete(e->ssep);
		e->ssep = NULL;
	}
	free(e);
}

noll_graph_t*
noll_graph_alloc(noll_var_array* lvars, noll_var_array* svars, uint_t nodes,
		uint_t edges, uint_t* vars) {

	noll_graph_t* res = (noll_graph_t*) malloc(sizeof(noll_graph_t));
	res->lvars = noll_var_array_new();
	noll_var_array_copy(res->lvars, lvars);
	res->svars = noll_var_array_new();
	noll_var_array_copy(res->svars, svars);
	// size of the adj matrices
	res->nodes_size = nodes;
	/*
	 * labeling of nodes by variables: fill mapping var2nodes
	 */
	if (!vars) {
		res->var2node = (uint_t*) malloc(noll_vector_size (lvars)
				* sizeof(uint_t));
		for (uint_t i = 0; i < noll_vector_size (lvars); i++)
			res->var2node[i] = UNDEFINED_ID;
	} else
		res->var2node = vars;
	/*
	 * allocate the array of edges
	 */
	res->edges = noll_edge_array_new();
	noll_edge_array_reserve(res->edges, edges);

	/*
	 * allocate the adjacency matrices
	 */
	res->mat = (noll_uid_array**) malloc(res->nodes_size
			* sizeof(noll_uid_array*));
	res->rmat = (noll_uid_array**) malloc(res->nodes_size
			* sizeof(noll_uid_array*));
	for (uint_t i = 0; i < res->nodes_size; i++) {
		res->mat[i] = NULL;
		res->rmat[i] = NULL;
	}

	/*
	 * allocate the difference edges, a low-diagonal matrix
	 */
	res->diff = (bool**) malloc(res->nodes_size * sizeof(bool*));
	for (uint_t i = 0; i < res->nodes_size; i++) {
		res->diff[i] = (bool*) malloc((i + 1) * sizeof(bool));
		for (uint_t j = 0; j <= i; j++)
			res->diff[i][j] = false;
	}
	/*
	 *  allocate the mapping of set variables to edges
	 */
	res->sloc2edge = (uint_t*) malloc(noll_vector_size(svars) * sizeof(uint_t));
	for (uint_t i = 0; i < noll_vector_size(svars); i++) {
		res->sloc2edge[i] = UNDEFINED_ID;
	}
	// allocate the sharing array
	res->share = noll_share_array_new();

	res->isComplete = false;
	return res;
}

void noll_graph_free(noll_graph_t* g) {

	noll_var_array_delete(g->lvars);
	g->lvars = NULL;
	noll_var_array_delete(g->svars);
	g->svars = NULL;
	if (g->var2node != NULL)
		free(g->var2node);
	for (uint_t i = 0; i < noll_vector_size(g->edges); i++) {
		if (g->mat[i] != NULL)
			noll_uid_array_delete(g->mat[i]);
		if (g->rmat[i] != NULL)
			noll_uid_array_delete(g->rmat[i]);
	}
	free(g->mat);
	free(g->rmat);
	noll_edge_array_delete(g->edges);
	if (g->diff != NULL)
		for (uint_t i = 0; i < g->nodes_size; i++) {
			free(g->diff[i]);
		}
	free(g->diff);
	if (g->sloc2edge != NULL)
		free(g->sloc2edge);
	if (g->share != NULL)
		noll_share_array_delete(g->share);
	free(g);
}

/* ====================================================================== */
/* Getters/setters */
/* ====================================================================== */

uint_t noll_graph_get_var(noll_graph_t* g, uint_t n) {
	for (uint_t vi = 0; vi < noll_vector_size(g->lvars); vi++)
		if (g->var2node[vi] == n)
			return vi;
	return UNDEFINED_ID;
}


/* ====================================================================== */
/* Printing */
/* ====================================================================== */

void noll_edge_fprint(FILE* f, noll_var_array* svars, noll_edge_t* e) {
	assert(f);
	assert(e);
	assert(e->args);
	switch (e->kind) {
	case NOLL_EDGE_PTO:
		fprintf(f, "%d: n%d.f%d==n%d", e->id, noll_vector_at(e->args,0),
				e->label, noll_vector_at(e->args,1));
		break;
	case NOLL_EDGE_PRED:
		fprintf(f, "%d: %s_%s(n%d,n%d", e->id, noll_pred_name(e->label),
				noll_vector_at(svars,e->bound_svar)->vname,
				noll_vector_at(e->args,0), noll_vector_at(e->args,1));
		if (e && e->args)
			for (uint_t i = 2; i < noll_vector_size (e->args); i++)
				fprintf(f, ",n%d", noll_vector_at (e->args, i));
		fprintf(f, ")");
		break;
	default:
		fprintf(f, "%d: error", e->id);
		break;
	}
}

void noll_edge_fprint_dot(FILE* f, noll_var_array* svars, noll_edge_t* e) {
	assert(f);
	assert(e);
	assert(e->args);
	fprintf(f, "n%d -> n%d [label=\"", noll_vector_at(e->args,0),
			noll_vector_at(e->args,1));
	noll_edge_fprint(f, svars, e);
	fprintf(f, "\"];\n");
}

void noll_share_fprint_dot(FILE* f, noll_var_array* lvars,
		noll_var_array* svars, noll_share_array* phi) {
	if (!phi) {
		fprintf(f, "null");
		return;
	}
	for (uint_t i = 0; i < noll_vector_size (phi); i++) {
		noll_share_atom_fprint(f, lvars, svars, noll_vector_at (phi, i));
		fprintf(f, " | ");
	}
	fprintf(f, " true");
	;
}

void noll_graph_fprint(FILE* f, noll_graph_t* g) {
	assert(f);
	if (!g) {
		fprintf(f, "\t null graph\n");
		return;
	}
	fprintf(f, "Graph nodes size: %d\n", g->nodes_size);

	fprintf(f, "Graph nodes labels:\n");
	for (uint_t i = 0; i < noll_vector_size (g->lvars); i++)
		fprintf(f, "%s(n%d),", noll_var_name(g->lvars, i, NOLL_TYP_RECORD),
				g->var2node[i]);
	fprintf(f, "\n");

	fprintf(f, "Graph difference edges: \n");
	assert(g->diff != NULL);
	// low-diagonal matrix
	for (uint_t i = 0; i < g->nodes_size; i++)
		for (uint_t j = 0; j <= i; j++)
			if (g->diff[i][j])
				fprintf(f, "\t\tn%d != n%d\n", i, j);

	fprintf(f, "Graph edges: \n");
	assert(g->edges);
	for (uint_t eid = 0; eid < noll_vector_size(g->edges); eid++) {
		noll_edge_fprint(f, g->svars, noll_vector_at (g->edges, eid));
		fprintf(f, "\n");
	}

	fprintf(f, "Graph sharing constraints: \n");
	if (g->share) {
		noll_share_fprint(f, g->lvars, g->svars, g->share);
	} else
		fprintf(f, "\t\tnull\n");

}

void noll_graph_fprint_dot(char* fname, noll_graph_t* g) {
	assert(fname);
	if (!g) {
		fprintf(stderr, "Null graph! quit.");
		return;
	}
	FILE* f = fopen(fname, "w");
	if (!f) {
		fprintf(stderr, "File %s not found! quit.", fname);
		return;
	}
	fprintf(f, "digraph %s {\nnode [shape=record];\n", fname);
	// print nodes
	for (uint_t n = 0; n < g->nodes_size; n++) {
		// print node n with its labels
		fprintf(f, "\tn%d [label=\"{n%d|", n, n);
		for (uint_t v = 0; v < noll_vector_size (g->lvars); v++)
			if (g->var2node[v] == n)
				fprintf(f, "%s ", noll_var_name(g->lvars, v, NOLL_TYP_RECORD));

		fprintf(f, "}\"];\n");
	}
	// print edges

	// fprintf(f, "Graph difference edges: \n");
	assert(g->diff != NULL);
	// low-diagonal matrix
	for (uint_t i = 0; i < g->nodes_size; i++)
		for (uint_t j = 0; j <= i; j++)
			if (g->diff[i][j])
				fprintf(f, "n%d -> n%d [style=dotted];\n", i, j);

	//fprintf(f, "Graph edges: \n");
	assert(g->edges);
	for (uint_t eid = 0; eid < noll_vector_size(g->edges); eid++) {
		noll_edge_fprint_dot(f, g->svars, noll_vector_at (g->edges, eid));
		fprintf(f, "\n");
	}

	fprintf(f, "\tshare [label=\"{share|");
	if (g->share) {
		noll_share_fprint_dot(f, g->lvars, g->svars, g->share);
	} else
		fprintf(f, "\t\tnull\n");
	fprintf(f, "}\"];\n");

	fprintf(f, "\n}\n");
	fflush(f);
	fclose(f);
	return;
}
