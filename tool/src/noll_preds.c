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

NOLL_VECTOR_DEFINE (noll_pred_array, noll_pred_t*)
;

/* ====================================================================== */
/* Globals */
/* ====================================================================== */

noll_pred_array* preds_array;

void noll_pred_init() {
	preds_array = noll_pred_array_new();
	noll_pred_array_reserve(preds_array, 4);
}

/* ====================================================================== */
/* Other methods */

/* ====================================================================== */

noll_pred_t*
noll_pred_new(const char* name, uid_t pid, noll_pred_binding_t* def) {
	noll_pred_t* p = (noll_pred_t*) malloc(sizeof(struct noll_pred_t));
	p->pname = strdup(name);
	p->pid = pid;
	p->def = def;
	// compute typing information
	p->typ = (noll_pred_typing_t*) malloc(sizeof(struct noll_pred_typing_t));
	p->typ->ptype0 = noll_var_record(p->def->vars, 0);
	p->typ->ptypes = noll_uid_array_new();
	p->typ->pfields0 = noll_uid_array_new();
	p->typ->pfields1 = noll_uid_array_new();
	noll_form_fill_type(p->def->sigma_0, p->typ->pfields0, NULL);
	noll_form_fill_type(p->def->sigma_0, NULL, p->typ->ptypes);
	noll_form_fill_type(p->def->sigma_1, p->typ->pfields1, p->typ->ptypes);
	return p;
}

uid_t noll_pred_array_find(const char* name) {
	if (preds_array && (noll_vector_size (preds_array) > 0)) {
		uint_t sz = noll_vector_size (preds_array);
		for (uint_t i = 0; i < sz; i++)
			if (noll_vector_at (preds_array, i) && !strcmp(name,
					noll_vector_at (preds_array, i)->pname))
				return i;
	}
	return UNDEFINED_ID;
}

uid_t noll_pred_register(const char* pname, noll_pred_binding_t* def) {
	assert (pname && def);
	uid_t pid = noll_vector_size (preds_array);
	noll_pred_t* p = noll_pred_new(pname, pid, def);
	noll_pred_array_push(preds_array, p);
	return pid;
}

uid_t noll_pred_typecheck_call(uid_t pid, uid_t* actuals_ty, uid_t size) {
	if (pid == UNDEFINED_ID)
		return UNDEFINED_ID;
	noll_pred_t* p = noll_vector_at (preds_array, pid);
	if (size != p->def->fargs) {
		// TODO: make error message
		printf(
				"Predicate call `%s': called with %d parameters instead of %d.\n",
				p->pname, size, p->def->fargs);
		return UNDEFINED_ID;
	}
	for (uint_t i = 0; i < size; i++) {
		noll_var_t* fi = noll_vector_at (p->def->vars, i);
		uid_t
				fi_ty =
						(fi->vty && fi->vty->kind == NOLL_TYP_RECORD) ? noll_vector_at (fi->vty->args, 0)
								: UNDEFINED_ID;
		if (actuals_ty[i] != fi_ty) {
			// TODO: make error message
			printf("Predicate call `%s': bad type for the %d-th parameter.\n",
					p->pname, i);
			return UNDEFINED_ID;
		}
	}
	return pid;
}

char*
noll_pred_name(uid_t pid) {
	if (pid >= noll_vector_size (preds_array)) {
		printf(
				"noll_pred_name: called with identifier %d not in the global environment.\n",
				pid);
		return "unknown";
	}
	return noll_vector_at (preds_array, pid)->pname;
}

/* ====================================================================== */
/* Printing */
/* ====================================================================== */

void noll_pred_array_fprint(FILE* f, noll_pred_array* a, const char* msg) {
	fprintf(f, "\n%s: ", msg);
	fflush(f);
	if (!a) {
		fprintf(f, "null\n");
		return;
	}
	fprintf(f, "[");
	uint_t length_a = noll_vector_size (a);
	for (uint_t i = 0; i < length_a; i++) {
		noll_pred_t* pi = noll_vector_at (a, i);
		fprintf(f, "pred-%d: %s(%zu args) ", pi->pid, pi->pname,
				pi->def->pargs);
		fprintf(f, "of type %s, ", noll_record_name(pi->typ->ptype0));
		fprintf(f, "\n\t\tall types [");
		if (pi->typ->ptypes != NULL)
			for (uint_t ti = 0; ti < noll_vector_size(pi->typ->ptypes); ti++)
				fprintf(f, "%s, ", noll_record_name(noll_vector_at(
						pi->typ->ptypes, ti)));
		fprintf(f, "], ");
		fprintf(f, "\n\t\trec fields [");
		if (pi->typ->pfields0 != NULL)
			for (uint_t fi = 0; fi < noll_vector_size(pi->typ->pfields0); fi++)
				fprintf(f, "%s, ", noll_field_name(noll_vector_at(
						pi->typ->pfields0, fi)));
		fprintf(f, "], ");
		fprintf(f, "\n\t\tnested fields [");
		if (pi->typ->pfields1 != NULL)
			for (uint_t fi = 0; fi < noll_vector_size(pi->typ->pfields1); fi++)
				fprintf(f, "%s, ", noll_field_name(noll_vector_at(
						pi->typ->pfields1, fi)));
		fprintf(f, "]\n ");
	}
	fprintf(f, " - ]");
	fflush(f);
}

