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

#ifndef NOLL2SAT_H_
#define NOLL2SAT_H_

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

#include "noll_vars.h"
#include "noll_types.h"
#include "noll_form.h"
#include "noll_preds.h"

/* ====================================================================== */
/* Types storing information about the boolean abstraction */
/* ====================================================================== */

/* information about the formula translated */
typedef struct noll_form_info_s {
	bool* used_lvar; /* bitset of size of locs_array */
	bool* used_svar; /* bitset of size of slocs_array */
	bool* used_pred; /* bitset of size of pred_array */
	bool* used_flds; /* bitset of size of fields_array */

	uint_t lvar_size; /* number of used lvar */
	uint_t svar_size; /* number of used svar */
	uint_t fld_size; /* number of used fields */
	uint_t pto_size; /* number of pto atoms */
	uint_t ls_size; /* number of pred atoms */

} noll_form_info_t;

/* pure atomic formula */
typedef struct noll_sat_pure_s {
	noll_pure_op_t op;
	uid_t x;
	uid_t y;
} noll_sat_pure_t;

NOLL_VECTOR_DECLARE(noll_sat_pure_array, noll_sat_pure_t*);

/* indexed space formula */
typedef struct noll_sat_space_s {
	noll_space_t* forig;
	union {
		uint_t idx; // for forig == pto
		struct {
			uid_t var; // UNDEFINED_ID if not apto
			uid_t fld;
		} p; // for forig == pred
	} m;
} noll_sat_space_t;

NOLL_VECTOR_DECLARE(noll_sat_space_array, noll_sat_space_t*);

/* [x in alpha] variable information */
typedef struct noll_sat_in_s {
	uid_t x; /* position in locs_array */
	uid_t alpha; /* position in slocs_array */
} noll_sat_in_t;

NOLL_VECTOR_DECLARE(noll_sat_in_array, noll_sat_in_t*);

typedef struct noll_sat_s {
	noll_form_t* form; /* formula for which the information is stored */
	char* fname; /* file name used to store the formula */
	FILE* file; /* if fname already open then != NULL, otherwise == NULL */
	noll_form_info_t* finfo; /* form information used in translation */
	uint_t no_clauses; /* number of clauses put in the file for F_sat */
	uint_t no_vars; /* number of vars used */

	/* encoding of constraints [x = y] for any x, y in environment */
	uint_t start_pure; /* id of first variable */
	uint_t size_pure; /* number of boolean variables */
	uid_t** var_pure; /* lower diagonal array [i][j] j <= i,
	 storing boolean var id */

	/* encoding of points-to atoms [x,f,y] of phi */
	uint_t start_pto; /* id of first variable */
	uint_t size_pto; /* number of variables, size of the array below */
	noll_sat_space_array* var_pto; /* sorted array of pto constraints [x,f,y] */

	/* encoding of predicate atoms [P,alpha,x,y,z] in phi */
	uint_t start_pred; /* id of first variable */
	uint_t size_pred; /* number of variables, size of the array below */
	noll_sat_space_array* var_pred; /* sorted array of pred atoms P_alpha(x,y,z) */

	/* encoding of anonymous points-to constraints [x,f,alpha]
	 * for any x,f,alpha s.t. ty(x)=ty_src(f) in ty_1(alpha), alpha bound in phi */
	uint_t start_apto; /* id of first variable */
	uint_t size_apto; /* number of variables, size of the array below */
	noll_sat_space_array* var_apto; /* sorted array of pto constraints [x,f,alpha] */

	/* encoding of sharing atoms [x in alpha] for any x, alpha in phi*/
	uint_t start_inset; /* id of first variable */
	uint_t size_inset; /* number of variables, size of the array below */
	noll_sat_in_array* var_inset; /* sorted array of sharing atoms x in alpha */

} noll_sat_t;

NOLL_VECTOR_DECLARE(noll_sat_array, noll_sat_t*);

/* ====================================================================== */
/* Globals */
/* ====================================================================== */

extern noll_sat_t* pabstr; // abstraction of the positive formula
extern noll_sat_t* nabstr; // abstraction of the negative formula

/* ====================================================================== */
/* Constructors/destructors */
/* ====================================================================== */

noll_sat_t* noll_sat_new(noll_form_t* phi);
/* Build a boolean abstraction for the given formula */
void noll_sat_free(noll_sat_t* a);
/* Free a boolean abstraction */

/* ====================================================================== */
/* Collect information for boolean abstraction */
/* ====================================================================== */

noll_sat_t* noll2sat_fill_bvar(noll_form_t* form, char* fname);
/* writes the boolean variables and fill sat informations */

/* ====================================================================== */
/* Printing the boolean abstraction */
/* ====================================================================== */

noll_sat_t* noll2sat(noll_form_t* form, char* fname);
/* writes the boolean abstraction of "form" in the file "fname" */

int noll2sat_pure(noll_sat_t* fsat);
/* writes the boolean abstraction of the pure part of "form": F(\Pi) and F_{eq} */

int noll2sat_space(noll_sat_t* fsat);
/* writes the boolean abstraction of the spatial part of "form": F(\Sigma) */

int noll2sat_membership(noll_sat_t* fsat);
/* writes the boolean abstraction of the membership constraints of "form": F_\in */

int noll2sat_det(noll_sat_t* fsat);
/* writes the boolean abstraction of the determinism constraints of "form": F_det */

int noll2sat_share(noll_sat_t* fsat);
/* writes the boolean abstraction of the sharing constraints of "form": F(\Lambda) */

/* ====================================================================== */
/* Calling Minisat and adding constraints */
/* ====================================================================== */

int noll2sat_is_eq(noll_sat_t* fsat, uid_t x, uid_t y, noll_pure_op_t oper);
/* Returns 1 if the boolean abstraction implies [x oper y]
 * returns 0, otherwise. The boolean abstraction fsat is
 * initialized before calling this function */

int noll2sat_is_sat(noll_sat_t* fsat);
/* Returns 1 if form is satisfiable using
 * the boolean abstraction in fsat */

int noll2sat_is_in(noll_sat_t* fsat, uid_t x, uid_t alpha);
/* Returns 1 if the boolean abstraction fsat
 * implies that x in alpha, otherwise return 0 */

noll_sat_t* noll2sat_normalize(noll_form_t* form, char* fname, bool incr,
		bool destructive);
/* Updates form to its normal form and
 * put in the file "file" the boolean abstraction;
 * use incremental minisat if incr = true */

#endif /* NOLL2SAT_H_ */
