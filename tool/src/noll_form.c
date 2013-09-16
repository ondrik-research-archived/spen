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
 * Abstract Syntax Tree of NOLL formulas.
 */

#include<sys/time.h>

#include "noll_form.h"
#include "noll_preds.h"
#include "noll2bool.h"
#include "noll2sat.h"
#include "noll2graph.h"
#include "noll_graph.h"

NOLL_VECTOR_DEFINE (noll_space_array, noll_space_t*)
;

NOLL_VECTOR_DEFINE (noll_share_array, noll_atom_share_t*)
;

NOLL_VECTOR_DEFINE (noll_sterm_array, noll_sterm_t*)
;

NOLL_VECTOR_DEFINE (noll_form_array, noll_form_t*)
;

/* ====================================================================== */
/* Globals */
/* ====================================================================== */

noll_form_t* noll_form_new() {
	noll_form_t* form = (noll_form_t*) malloc(sizeof(noll_form_t));
	form->kind = NOLL_FORM_VALID;
	form->lvars = noll_var_array_new();
	form->svars = noll_var_array_new();
	form->pure = NULL; //noll_pure_new();
	form->space = noll_space_new();
	form->share = noll_share_new();

	return form;
}

void noll_form_free(noll_form_t* form) {
	assert (form != NULL);
	if (form->lvars != NULL) {
		noll_var_array_delete(form->lvars);
		form->lvars = NULL;
	}
	if (form->svars != NULL) {
		noll_var_array_delete(form->svars);
		form->svars = NULL;
	}
	if (form->pure != NULL) {
		noll_pure_free(form->pure);
		form->pure = NULL;
	}
	if (form->space != NULL) {
		noll_space_free(form->space);
		form->space = NULL;
	}
	if (form->share != NULL) {
		noll_share_free(form->share);
		form->share = NULL;
	}
	free(form);
}

void noll_form_set_unsat(noll_form_t* form) {

	form->kind = NOLL_FORM_UNSAT;
	// DO NOT FREE variables, already pointed by the context
	if (form->pure != NULL) {
		noll_pure_free(form->pure);
		form->pure = NULL;
	}
	if (form->space != NULL) {
		noll_space_free(form->space);
		form->space = NULL;
	}
	if (form->share != NULL) {
		noll_share_free(form->share);
		form->share = NULL;
	}
}

noll_pure_t*
noll_pure_new(uint_t size) {
	noll_pure_t* ret = (noll_pure_t*) malloc(sizeof(struct noll_pure_t));
	ret->m = NULL;
	ret->size = size;
	if (ret->size > 0) {
		ret->m = (noll_pure_op_t**) malloc(ret->size * sizeof(noll_pure_op_t*));
		for (uid_t i = 0; i < ret->size; i++) {
			uid_t sz = ret->size - i;
			ret->m[i] = (noll_pure_op_t*) malloc(sz * sizeof(noll_pure_op_t));
			// set the diagonal
			ret->m[i][0] = NOLL_PURE_EQ;
			for (uid_t j = 1; j < sz; j++)
				ret->m[i][j] = NOLL_PURE_OTHER;
		}
	}
	return ret;
}

void noll_pure_free(noll_pure_t* p) {
	if (!p)
		return;
	if (p->m) {
		for (uid_t i = 0; i < p->size; i++)
			if (p->m[i])
				free(p->m[i]);

		free(p->m);
	}
	free(p);
}

noll_space_t* noll_space_new() {
	noll_space_t* ret = (noll_space_t*) malloc(sizeof(noll_space_t));
	ret->kind = NOLL_SPACE_EMP;
	ret->is_precise = true;
	return ret;
}

void noll_space_free(noll_space_t* s) {
	if (!s)
		return;
	switch (s->kind) {
	case NOLL_SPACE_PTO: {
		if (noll_vector_size (s->m.pto.fields) > 0) {
			if (s->m.pto.fields)
				noll_uid_array_delete(s->m.pto.fields);
			if (s->m.pto.dest)
				noll_uid_array_delete(s->m.pto.dest);
		}
		break;
	}
	case NOLL_SPACE_LS: {
		if (s->m.ls.args && noll_vector_size (s->m.ls.args) > 0)
			noll_uid_array_delete(s->m.ls.args);
		break;
	}
	case NOLL_SPACE_WSEP:
	case NOLL_SPACE_SSEP: {
		noll_space_array_delete(s->m.sep);
		break;
	}
	default:
		break;
	}
	free(s);
	return;
}

noll_sterm_t*
noll_sterm_new_var(uid_t v, noll_sterm_kind_t kind) {
	noll_sterm_t* tv = (noll_sterm_t*) malloc(sizeof(noll_sterm_t));
	tv->kind = kind;
	tv->lvar = (kind == NOLL_STERM_LVAR) ? v : UNDEFINED_ID;
	tv->svar = (kind == NOLL_STERM_SVAR) ? v : UNDEFINED_ID;
	return tv;
}

noll_sterm_t*
noll_sterm_new_prj(uid_t s, uid_t v) {
	noll_sterm_t* tv = (noll_sterm_t*) malloc(sizeof(noll_sterm_t));
	tv->kind = NOLL_STERM_PRJ;
	tv->lvar = v;
	tv->svar = s;
	return tv;
}

noll_share_array* noll_share_new() {
	return noll_share_array_new();
}

void noll_share_free(noll_share_array* s) {
	if (s == NULL)
		return;
	// TODO: free also the sterms in each element
	noll_share_array_delete(s);
}

noll_sterm_t*
noll_sterm_copy(noll_sterm_t* a) {
	if (a == NULL)
		return NULL;

	noll_sterm_t* tv = (noll_sterm_t*) malloc(sizeof(noll_sterm_t));
	tv->kind = a->kind;
	tv->lvar = a->lvar;
	tv->svar = a->svar;
	return tv;
}

void noll_pure_update_eq(noll_form_t* f, uid_t l, uid_t c) {
	assert (f);
	if (f->kind == NOLL_FORM_UNSAT)
		return;
	assert (f->pure && f->pure->m);
	assert ((l < f->pure->size) && (c < f->pure->size) && (l < c));
	if (noll_pure_matrix_at (f->pure, l, c) == NOLL_PURE_NEQ) {
#ifndef NDEBUG
		fprintf (stdout, "noll_pure_update_eq(%d,%d): set unsat!\n", l, c);
#endif
		noll_form_set_unsat(f);
		return;
	}
	noll_pure_matrix_at (f->pure, l, c) = NOLL_PURE_EQ;
}

void noll_pure_update_neq(noll_form_t* f, uid_t l, uid_t c) {
	assert (f);
	if (f->kind == NOLL_FORM_UNSAT)
		return;
	assert (f->pure && f->pure->m);
	assert ((l < f->pure->size) && (c < f->pure->size) && (l < c));
	if (noll_pure_matrix_at (f->pure, l, c) == NOLL_PURE_EQ) {
#ifndef NDEBUG
		fprintf (stdout, "noll_pure_update_neq(%d,%d): set unsat!\n", l, c);
#endif
		noll_form_set_unsat(f);
		return;
	}
	noll_pure_matrix_at (f->pure, l, c) = NOLL_PURE_NEQ;
}

void noll_pure_add_eq(noll_form_t* f, uid_t v1, uid_t v2) {
	assert (f != NULL);
	if (f->kind == NOLL_FORM_UNSAT)
		return;

	/* part used only at parsing
	 uint_t size = noll_vector_size(f->lvars);
	 if ((f->pure != NULL) && (f->pure->size != size)) {
	 noll_pure_free(f->pure);
	 f->pure = NULL;
	 }
	 if (f->pure == NULL)
	 f->pure = noll_pure_new(size);
	 */

	assert (f->pure->size > v1 && f->pure->size > v2);
	if (v1 != v2) {
		// set the entry in form->pure->m to 0
		uid_t v_lin = (v1 <= v2) ? v1 : v2;
		uid_t v_col = (v1 <= v2) ? v2 : v1;
		noll_pure_update_eq(f, v_lin, v_col);
		// close with entries < vcol-1
		for (uid_t j = v_lin + 1; (j < v_col) && (f->kind != NOLL_FORM_UNSAT); j++) {
			if (noll_pure_matrix_at (f->pure, v_lin, j) == NOLL_PURE_EQ)
				/* v_lin = v_col && v_lin = j => j = v_col */
				noll_pure_update_eq(f, j, v_col);

			if (noll_pure_matrix_at (f->pure, v_lin, j) == NOLL_PURE_NEQ)
				/* v_lin = v_col && v_lin != j => j != v_col */
				noll_pure_update_neq(f, j, v_col);
		}
		// close with entries > vcol
		for (uid_t j = v_col + 1; (j < f->pure->size) && (f->kind
				!= NOLL_FORM_UNSAT); j++) {
			if (noll_pure_matrix_at (f->pure, v_lin, j) == NOLL_PURE_EQ)
				/* v_lin = v_col && v_lin = j =>  v_col = j */
				noll_pure_update_eq(f, v_col, j);

			if (noll_pure_matrix_at (f->pure, v_lin, j) == NOLL_PURE_NEQ)
				/* v_lin = v_col && v_lin != j => j != v_col */
				noll_pure_update_neq(f, v_col, j);

			if (noll_pure_matrix_at (f->pure, v_col, j) == NOLL_PURE_EQ)
				/* v_lin = v_col && v_col = j =>  v_lin = j */
				noll_pure_update_eq(f, v_lin, j);

			if (noll_pure_matrix_at (f->pure, v_col, j) == NOLL_PURE_NEQ)
				/* v_lin = v_col && v_col != j => v_lin != j */
				noll_pure_update_neq(f, v_lin, j);
		}
	}
	if (f->kind != NOLL_FORM_UNSAT)
		f->kind = NOLL_FORM_SAT;
}

void noll_pure_add_neq(noll_form_t* f, uid_t v1, uid_t v2) {
	assert (f != NULL);
	if (f->kind == NOLL_FORM_UNSAT)
		return;

	/* part used only at parsing
	 unt_t size = noll_vector_size(f->lvars);
	 if (f->pure != NULL)
	 if (f->pure->size != size) {
	 noll_pure_free(f->pure);
	 f->pure = NULL;
	 }
	 if (f->pure == NULL)
	 f->pure = noll_pure_new(size);
	 */

	assert (f->pure->size > v1 && f->pure->size > v2);
	// set the entry in form->pure->m to 0
	uid_t v_lin = (v1 <= v2) ? v1 : v2;
	uid_t v_col = (v1 <= v2) ? v2 : v1;
	if (v_lin == v_col) {
		// try to add x != x
#ifndef NDEBUG
		fprintf (stdout, "noll_pure_add_neq(%d,%d): set unsat!\n", v1, v2);
#endif
		noll_form_set_unsat(f);
		return;
	}
	noll_pure_update_neq(f, v_lin, v_col);
	// close with entries < vcol-1
	for (uid_t j = v_lin + 1; (f->kind != NOLL_FORM_UNSAT) && (j < v_col); j++) {
		if (noll_pure_matrix_at (f->pure, v_lin, j) == NOLL_PURE_EQ)
			/* v_lin != v_col && v_lin = j => j != v_col */
			noll_pure_update_neq(f, j, v_col);
	}
	// close with entries > vcol
	for (uid_t j = v_col + 1; (f->kind != NOLL_FORM_UNSAT) && (j
			< f->pure->size); j++) {
		if (noll_pure_matrix_at (f->pure, v_lin, j) == NOLL_PURE_EQ)
			/* v_lin != v_col && v_lin = j =>  v_col != j */
			noll_pure_update_neq(f, v_col, j);

		if (noll_pure_matrix_at (f->pure, v_col, j) == NOLL_PURE_EQ)
			/* v_lin != v_col && v_col = j =>  v_lin != j */
			noll_pure_update_neq(f, v_lin, j);
	}
	if (f->kind != NOLL_FORM_UNSAT)
		f->kind = NOLL_FORM_SAT;
}

/* ====================================================================== */
/* Typing */
/* ====================================================================== */

/**
 * Fill the arguments flds and typs, if not null, with the
 * fields resp. record ids, obtained from formula form.
 * @param form   formula
 * @param flds   array of fields to be filled
 * @param typs   array of types to be filled
 */
void noll_form_fill_type(noll_space_t* form, noll_uid_array* flds,
		noll_uid_array* typs) {
	if (!form || form->kind == NOLL_SPACE_EMP)
		return;
	switch (form->kind) {
	case NOLL_SPACE_PTO: {
		for (uid_t i = 0; i < noll_vector_size (form->m.pto.fields); i++) {
			uid_t fid = noll_vector_at (form->m.pto.fields, i);
			noll_field_t* f = noll_vector_at (fields_array, fid);
			if (flds)
				noll_uid_array_cup(flds, fid);
			if (typs)
				noll_uid_array_cup(typs, f->src_r);
		}
		break;
	}
	case NOLL_SPACE_LS: {
		noll_pred_t* pred = noll_vector_at (preds_array, form->m.ls.pid);
		if (pred && pred->typ) {
			// copy pred information in the arrays
			if (pred->typ->pfields0)
				for (uid_t i = 0; i < noll_vector_size (pred->typ->pfields0); i++) {
					uid_t f = noll_vector_at (pred->typ->pfields0, i);
					if (flds)
						noll_uid_array_cup(flds, f);
				}
			if (pred->typ->pfields1)
				for (uid_t i = 0; i < noll_vector_size (pred->typ->pfields1); i++) {
					uid_t f = noll_vector_at (pred->typ->pfields1, i);
					if (flds)
						noll_uid_array_cup(flds, f);
				}
			if (pred->typ->ptype0 != UNDEFINED_ID)
				if (typs)
					noll_uid_array_cup(typs, pred->typ->ptype0);
			if (pred->typ->ptypes)
				for (uid_t i = 0; i < noll_vector_size (pred->typ->ptypes); i++) {
					uid_t t = noll_vector_at (pred->typ->ptypes, i);
					if (typs)
						noll_uid_array_cup(typs, t);
				}
		}
		break;
	}
	default: {
		// separation formula
		for (uid_t i = 0; i < noll_vector_size (form->m.sep); i++)
			noll_form_fill_type(noll_vector_at (form->m.sep, i), flds, typs);
		break;
	}
	}
	return;
}

/* ====================================================================== */
/* Getters/Setters */
/* ====================================================================== */

int noll_form_array_is_unsat(noll_form_array* phi1_phiN) {
	assert (phi1_phiN != NULL);

	/* all formulae shall be unsat */
	for (int i = 0; i < noll_vector_size(phi1_phiN); i++)
		if (noll_vector_at(phi1_phiN,i)->kind != NOLL_FORM_UNSAT)
			return 0;
	return 1;
}

int noll_form_array_is_valid(noll_form_array* phi1_phiN) {
	assert (phi1_phiN != NULL);

	/* one formula shall be valid */
	for (int i = 0; i < noll_vector_size(phi1_phiN); i++)
		if (noll_vector_at(phi1_phiN,i)->kind == NOLL_FORM_VALID)
			return 1;
	return 0;
};


/* ====================================================================== */
/* Printing */

/* ====================================================================== */

void noll_pure_fprint(FILE* f, noll_var_array* lvars, noll_pure_t* phi) {
	if (!phi || !phi->m) {
		fprintf(f, "null\n");
		return;
	}
	for (uid_t l = 0; l < phi->size; l++)
		for (uid_t c = l; c < phi->size; c++) {
			fprintf(f, "%s", noll_var_name(lvars, l, NOLL_TYP_RECORD));
			switch (noll_pure_matrix_at (phi, l, c)) {
			case NOLL_PURE_EQ:
				fprintf(f, "=");
				break;
			case NOLL_PURE_NEQ:
				fprintf(f, "<>");
				break;
			default:
				fprintf(f, "#");
				break;
			}
			fprintf(f, "%s, ", noll_var_name(lvars, c, NOLL_TYP_RECORD));
		}
	fprintf(f, "\n");
}

void noll_space_fprint(FILE* f, noll_var_array* lvars, noll_var_array* svars,
		noll_space_t* phi) {
	if (!phi) {
		fprintf(f, "null\n");
		return;
	}

	if (phi->is_precise == true)
		fprintf(f, "[precise] ");
	else
		fprintf(f, "[junk] ");

	switch (phi->kind) {
	case NOLL_SPACE_EMP:
		fprintf(f, "emp");
		break;
	case NOLL_SPACE_JUNK:
		fprintf(f, "junk");
		break;
	case NOLL_SPACE_PTO: {
		fprintf(f, "(pto  ");
		if (lvars == NULL)
			fprintf(f, "*%d ...)", phi->m.pto.sid);
		else
			fprintf(f, "%s ...)", noll_vector_at(lvars,phi->m.pto.sid)->vname);
		break;
	}
	case NOLL_SPACE_LS: {
		noll_pred_t* pred = noll_vector_at (preds_array, phi->m.ls.pid);
		fprintf(f, "(%s_", pred->pname);
		if (svars == NULL)
			fprintf(f, "*%d", phi->m.ls.sid);
		else
			fprintf(f, "%s", noll_vector_at (svars, phi->m.ls.sid)->vname);
		for (uid_t i = 0; i < noll_vector_size (phi->m.ls.args); i++) {
			uint_t vi = noll_vector_at (phi->m.ls.args, i);
			if (lvars == NULL)
				fprintf(f, " *%d ", vi);
			else
				fprintf(f, " %s ", noll_vector_at (lvars, vi)->vname);
		}
		fprintf(f, ")");
		break;
	}
	default: {
		assert (phi->kind == NOLL_SPACE_WSEP || phi->kind == NOLL_SPACE_SSEP);
		if (phi->kind == NOLL_SPACE_WSEP)
			fprintf(f, "(wsep ");
		else
			fprintf(f, "(ssep ");
		for (uid_t i = 0; i < noll_vector_size (phi->m.sep); i++) {
			noll_space_fprint(f, lvars, svars, noll_vector_at (phi->m.sep, i));
			fprintf(f, "\n\t");
		}
		fprintf(f, ")");
		break;
	}
	}
}

void noll_share_sterm_fprint(FILE* f, noll_var_array* lvars,
		noll_var_array* svars, noll_sterm_t * t) {
	assert (t);
	switch (t->kind) {
	case NOLL_STERM_LVAR:
		fprintf(f, " %s ", noll_var_name(lvars, t->lvar, NOLL_TYP_RECORD));
		break;
	case NOLL_STERM_SVAR:
		fprintf(f, " %s ", noll_var_name(svars, t->svar, NOLL_TYP_SETLOC));
		break;
	case NOLL_STERM_PRJ:
		fprintf(f, " (prj %s %s) ", noll_var_name(svars, t->svar,
				NOLL_TYP_SETLOC),
				noll_var_name(lvars, t->lvar, NOLL_TYP_RECORD));
		break;
	default:
		fprintf(f, "error");
		break;
	}
}

void noll_share_sterm_array_fprint(FILE* f, noll_var_array* lvars,
		noll_var_array* svars, noll_sterm_array * t) {
	assert (t);
	if (noll_vector_size (t) > 1)
		fprintf(f, "(unloc ");

	for (uid_t i = 0; i < noll_vector_size (t); i++) {
		noll_share_sterm_fprint(f, lvars, svars, noll_vector_at (t, i));
		// fprintf (f, "\n");
	}

	if (noll_vector_size (t) > 1)
		fprintf(f, " )");
}

void noll_share_atom_fprint(FILE* f, noll_var_array* lvars,
		noll_var_array* svars, noll_atom_share_t * phi) {
	assert (phi);
	fprintf(f, "(");
	switch (phi->kind) {
	case NOLL_SHARE_IN:
		fprintf(f, "inloc ");
		break;
	case NOLL_SHARE_NI:
		fprintf(f, "not-inloc ");
		break;
	case NOLL_SHARE_SUBSET:
		fprintf(f, "leloc ");
		break;
	default:
		fprintf(f, "error ");
		break;
	}
	// fprintf (f, "\n\t");
	noll_share_sterm_fprint(f, lvars, svars, phi->t_left);
	// fprintf (f, "\n\t");
	noll_share_sterm_array_fprint(f, lvars, svars, phi->t_right);
	fprintf(f, ")");
}

void noll_share_fprint(FILE* f, noll_var_array* lvars, noll_var_array* svars,
		noll_share_array * phi) {
	if (!phi) {
		fprintf(f, "null\n");
		return;
	}
	for (uid_t i = 0; i < noll_vector_size (phi); i++) {
		noll_share_atom_fprint(f, lvars, svars, noll_vector_at (phi, i));
		fprintf(f, " &&\n");
	}
	fprintf(f, " true\n");
}

void noll_form_fprint(FILE* f, noll_form_t* phi) {
	assert (f != NULL);

	if (!phi) {
		fprintf(stdout, "null\n");
		return;
	}

	switch (phi->kind) {
	case NOLL_FORM_UNSAT:
		fprintf(f, "unsat\n");
		break;
	case NOLL_FORM_SAT:
		fprintf(f, "sat\n");
		break;
	case NOLL_FORM_VALID:
		fprintf(f, "valid\n");
		break;
	default:
		fprintf(f, "error\n");
		break;
	}
	fprintf(f, "\n\t lvars: ");
	noll_var_array_fprint(f, phi->lvars, "lvars");
	fprintf(f, "\n\t svars: ");
	noll_var_array_fprint(f, phi->svars, "svars");
	fprintf(f, "\n\t pure part: ");
	noll_pure_fprint(f, phi->lvars, phi->pure);
	fprintf(f, "\n\t shape part: ");
	noll_space_fprint(f, phi->lvars, phi->svars, phi->space);
	fprintf(f, "\n\t share part: ");
	noll_share_fprint(f, phi->lvars, phi->svars, phi->share);

}
