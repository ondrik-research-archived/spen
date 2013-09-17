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

#ifndef _NOLL_FORM_H_
#define	_NOLL_FORM_H_

#ifdef	__cplusplus
extern "C"
{
#endif

#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>
#include <stdio.h>
#include "noll_vars.h"
#include "noll_types.h"

/* ====================================================================== */
/* Datatypes */
/* ====================================================================== */

/** Pure atomic formulas.
 *  Encoded as an upper diagonal matrix of size = nb variables:
 *  for (v1(id) < v2(id))
 *    m[v1][v2] = NOLL_PURE_EQ if v1=v2,
 *                NOLL_PURE_NEQ if v1 != v2,
 *                NOLL_PURE_OTHER (-1) if unknown
 */
typedef enum noll_pure_op_t {
	NOLL_PURE_EQ = 0, NOLL_PURE_NEQ, NOLL_PURE_OTHER
} noll_pure_op_t;

typedef struct noll_pure_t {
	noll_pure_op_t** m; // matrix of equality and inequality constraints
	uint_t size; // allocated size for the matrix, 0 if empty or == locs_array size
} noll_pure_t;

/**
 * For variable i <= j, the matrix p->m stores an array of size-i cells!
 */
#define noll_pure_matrix_at(p,i,j) p->m[i][j-i]

/**
 * Spatial formulas.
 */

typedef struct noll_space_s noll_space_t; /* forward definition */
NOLL_VECTOR_DECLARE (noll_space_array, noll_space_t*)
;

typedef enum noll_space_op_t {
	NOLL_SPACE_EMP = 0,
	NOLL_SPACE_JUNK,
	NOLL_SPACE_PTO,
	NOLL_SPACE_LS,
	NOLL_SPACE_WSEP,
	NOLL_SPACE_SSEP,
	NOLL_SPACE_OTHER
/* NOT TO BE USED */
} noll_space_op_t;

// points-to constraint

typedef struct noll_pto_t {
	uid_t sid; // source location
	noll_uid_array* fields; // array of fields
	noll_uid_array* dest; // array of destination locations
} noll_pto_t;

// list segment constraint

typedef struct noll_ls_t {
	uid_t pid; // predicate
	noll_uid_array* args; // arguments used
	uid_t sid; // set of locations variable bound
} noll_ls_t;

struct noll_space_s {
	noll_space_op_t kind;
	bool is_precise;

	union {
		noll_pto_t pto; // points-to constraint
		noll_ls_t ls; // list segment constraint
		noll_space_array* sep; // array of constraints
	// for weak or strong separation
	} m;
};

/** Sharing formulas.
 */
typedef enum noll_share_op_t {
	NOLL_SHARE_IN = 0, /* \in */
	NOLL_SHARE_NI, /* \not\in */
	NOLL_SHARE_SUBSET, /* \subseteq */
	NOLL_SHARE_OTHER
/* NOT TO BE USED */
} noll_share_op_t;

typedef enum noll_sterm_kind_t {
	NOLL_STERM_LVAR = 0, NOLL_STERM_SVAR, NOLL_STERM_PRJ, NOLL_STERM_OTHER
/* NOT TO BE USED */
} noll_sterm_kind_t;

/**
 * Type for set of location terms.
 * Warning: because smtlib does not allow to use type names,
 * we use a location variable to obtain the type on which the projection
 * of the set of location variables shall be done.
 */
typedef struct noll_sterm_t {
	noll_sterm_kind_t kind;
	uid_t lvar; // location variable, UNDEFINED_ID if kind == NOLL_STERM_SVAR
	uid_t svar; // set of locations variable, UNDEFINED_ID if kind == NOLL_STERM_LVAR
} noll_sterm_t;

NOLL_VECTOR_DECLARE (noll_sterm_array, noll_sterm_t*)
;

/**
 * Type for sharing constraints.
 * Normal form used: term op (union of terms)
 */
typedef struct noll_atom_share_t {
	noll_share_op_t kind; // kind of constraint
	noll_sterm_t* t_left; // term left
	noll_sterm_array* t_right; // term right = union of terms
} noll_atom_share_t;

NOLL_VECTOR_DECLARE (noll_share_array, noll_atom_share_t*)
;

typedef enum noll_form_kind_t {
	NOLL_FORM_UNSAT = 0, NOLL_FORM_SAT, NOLL_FORM_VALID, NOLL_FORM_OTHER
/* NOT TO BE USED */
} noll_form_kind_t;

/** Formula in NOLL */
typedef struct noll_form_t {
	noll_form_kind_t kind; // kind of formula
	noll_var_array* lvars; // local variables
	noll_var_array* svars;
	noll_pure_t* pure; // pure part
	noll_space_t* space; // space part
	noll_share_array* share; // sharing part
} noll_form_t;

NOLL_VECTOR_DECLARE (noll_form_array, noll_form_t*)
;

/* ====================================================================== */
/* Constructors/destructors */
/* ====================================================================== */

noll_form_t* noll_form_new(void);
noll_pure_t* noll_pure_new(uint_t size);
noll_space_t* noll_space_new(void);
noll_share_array* noll_share_new(void);
noll_sterm_t* noll_sterm_new_var(uid_t v, noll_sterm_kind_t kind);
noll_sterm_t* noll_sterm_new_prj(uid_t s, uid_t v);
/* Allocation */

void noll_form_free(noll_form_t* f);
void noll_form_set_unsat(noll_form_t* f);
void noll_pure_free(noll_pure_t* p);
void noll_space_free(noll_space_t* s);
void noll_share_free(noll_share_array* s);
/* Deallocation */

noll_sterm_t* noll_sterm_copy(noll_sterm_t* a);
/* Copy */

void noll_pure_add_eq(noll_form_t* form, uid_t v1, uid_t v2);
void noll_pure_add_neq(noll_form_t* form, uid_t v1, uid_t v2);
/* Add equality/inequality pure formula */

/* ====================================================================== */
/* Typing */
/* ====================================================================== */

void noll_form_fill_type(noll_space_t* form, noll_uid_array* flds,
		noll_uid_array* typs);
/* Fill the typing information about the formula used in the predicate.
 */

/* ====================================================================== */
/* Getters/Setters */
/* ====================================================================== */

inline int noll_form_is_unsat(noll_form_t* phi) {
	return phi->kind == NOLL_FORM_UNSAT;
}
inline int noll_form_is_sat(noll_form_t* phi) {
	return phi->kind == NOLL_FORM_SAT;
}
inline int noll_form_is_valid(noll_form_t* phi) {
	return phi->kind == NOLL_FORM_VALID;
}

int noll_form_array_is_unsat(noll_form_array* phi1_phiN);
/* All formulae shall be unsat */
int noll_form_array_is_valid(noll_form_array* phi1_phiN);
/* One formula shall be valid */


/* ====================================================================== */
/* Printing */
/* ====================================================================== */

void noll_share_atom_fprint(FILE* f, noll_var_array* lvars,
		noll_var_array* svars, noll_atom_share_t * phi);
void noll_share_fprint(FILE* f, noll_var_array* lvars, noll_var_array* svars,
		noll_share_array * phi);
void noll_space_fprint(FILE* f, noll_var_array* lvars, noll_var_array* svars,
		noll_space_t* phi);
void noll_form_fprint(FILE* f, noll_form_t* phi);

#ifdef	__cplusplus
}
#endif

#endif	/* _NOL_FORMULA_H_ */

