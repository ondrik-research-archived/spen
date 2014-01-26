/**************************************************************************/
/*                                                                        */
/*  NOLL decision procedure                                               */
/*                                                                        */
/*  Copyright (C) 2013                                                    */
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
 * Defines the problem for the decision procedure.
 */

#include <sys/time.h>
#include <stdio.h>
#include "noll_entl.h"
#include "noll2bool.h" // for old normalization call
#include "noll2graph.h"
#include "noll_hom.h"

/* ====================================================================== */
/* Globals */
/* ====================================================================== */

noll_entl_t* noll_prob; // problem of entailment in noll

bool tosat_old = true; /* choice of boolean abstraction */

/* ====================================================================== */
/* Constructors/destructors */
/* ====================================================================== */

/* Initialization/Deallocation of problem */
void noll_entl_init() {
	noll_prob = (noll_entl_t*) malloc(sizeof(noll_entl_t));
	// init file name
	noll_prob->smt_fname = NULL;

	// init positive formula
	noll_prob->pform = noll_form_new();

	// init negative formulae array
	noll_prob->nform = noll_form_array_new();
	noll_form_array_push(noll_prob->nform, noll_form_new());

	// init command
	noll_prob->cmd = NOLL_FORM_SAT; // by default value
}

/**
 * Free memory allocated for entailment checking
 */
void noll_entl_free_aux(void) {

	assert(noll_prob != NULL);
	if (noll_prob->pabstr != NULL) {
		noll_sat_free(noll_prob->pabstr);
		noll_prob->pabstr = NULL;
	}
	if (noll_prob->nabstr != NULL) {
		noll_sat_array_delete(noll_prob->nabstr);
		noll_prob->nabstr = NULL;
	}
	if (noll_prob->pgraph != NULL) {
		noll_graph_free(noll_prob->pgraph);
		noll_prob->pgraph = NULL;
	}
	if (noll_prob->ngraph != NULL) {
		noll_graph_array_delete(noll_prob->ngraph);
		noll_prob->ngraph = NULL;
	}
}

void noll_entl_free(void) {
	assert(noll_prob != NULL);
	// this procedure shall be called only once
	if (noll_prob->smt_fname != NULL) {
		free(noll_prob->smt_fname);
		noll_prob->smt_fname = NULL;
	}
	if (noll_prob->pform != NULL) {
		noll_form_free(noll_prob->pform);
		noll_prob->pform = NULL;
	}
	if (noll_prob->nform != NULL) {
		noll_form_array_delete(noll_prob->nform);
		noll_prob->nform = NULL;
	}
	noll_entl_free_aux();
	free(noll_prob);
}

/* ====================================================================== */
/* Getters */
/* ====================================================================== */

noll_form_t* noll_entl_get_pform() {
	assert(noll_prob != NULL);
	return noll_prob->pform;
}

noll_form_t* noll_entl_get_nform_last() {
	assert(noll_prob != NULL);
	return noll_vector_last(noll_prob->nform);
}

noll_form_array* noll_entl_get_nform() {
	assert(noll_prob != NULL);
	return noll_prob->nform;
}

/* ====================================================================== */
/* Setters */
/* ====================================================================== */

void noll_entl_set_fname(char* fname) {
	noll_prob->smt_fname = fname;
}
void noll_entl_set_cmd(noll_form_kind_t pb) {
	noll_prob->cmd = pb;
}


/* ====================================================================== */
/* Printers */
/* ====================================================================== */

void noll_entl_fprint(FILE* f) {
	assert(f != NULL);

	if (noll_prob == NULL) {
		fprintf(f, "*** (entailment) null\n");
		return;
	}

	fprintf(f, "*** (source %s) check-%s on:\n", noll_prob->smt_fname,
			(noll_prob->cmd == NOLL_FORM_SAT) ? "sat" : "unsat");

	noll_records_array_fprint(f, "records:");
	noll_fields_array_fprint(f, "fields:");
	noll_pred_array_fprint(f, preds_array, "predicates:");

	fprintf(f, "\nFormula 1: ");
	noll_form_fprint(f, noll_prob->pform);
	fflush(f);
	fprintf(f, "\nFormulae 0: ");
	for (size_t i = 0; i < noll_vector_size(noll_prob->nform); i++) {
		fprintf(f, "\n\\/ (0-%zu): ", i);
		noll_form_fprint(f, noll_vector_at(noll_prob->nform,i));
	}
	fflush(stdout);
}

/* ====================================================================== */
/* Solver */
/* ====================================================================== */

/**
 * compute the difference between two times.
 *
 * @return 1 if the difference is negative, otherwise 0.
 */
int time_difference(struct timeval *result, struct timeval *t2,
		struct timeval *t1) {
	long int diff = (t2->tv_usec + 1000000 * t2->tv_sec)
			- (t1->tv_usec + 1000000 * t1->tv_sec);
	result->tv_sec = diff / 1000000;
	result->tv_usec = diff % 1000000;

	return (int) (diff < 0);
}

int noll_share_check_euf_decl(noll_var_array* lvars, noll_var_array* svars,
		char* fname) {
	FILE* out_decl = fopen(fname, "a");
	fprintf(out_decl, "(set-logic UFNIA)\n");
	fprintf(out_decl, "(declare-sort addr 0)\n");

	for (uint_t iterator = 0; iterator < noll_vector_size (svars); iterator++) {
		fprintf(out_decl, "(declare-fun %s (addr) Bool)\n",
				noll_vector_at(svars,iterator)->vname);
		/* some part of the extension to alpha(R)
		 for (uint_t it = 0; it < noll_vector_size (records_array); it++)
		 {
		 printf("in loop on exterior: type %s in %s\n",noll_vector_at(records_array,it)->name, noll_vector_at(slocs_array,iterator)->vname);
		 if (type_in_predicate_of_svar(it,iterator) == 1)
		 {
		 fprintf(out_decl,"(declare-fun %s_of_%s (addr) Bool)\n",noll_vector_at(slocs_array,iterator)->vname,noll_vector_at(records_array,it)->name);
		 }
		 }*/
	}

	for (uint_t iterator = 0; iterator < noll_vector_size (lvars); iterator++) {
		fprintf(out_decl, "(declare-fun %s () addr)\n",
				noll_vector_at(lvars,iterator)->vname);
	}
	fclose(out_decl);
	return 1;
}

int noll_share_check_euf_asserts(noll_var_array* lvars, noll_var_array* svars,
		noll_share_array* share, char* fname, int sign) {
	if (share == NULL)
		return 0;

	FILE* out_decl = fopen(fname, "a");

	for (uint_t iterator = 0; iterator < noll_vector_size (share); iterator++) {
		//printf("#@$#@$@#$@#$\n");
		noll_atom_share_t* atom = noll_vector_at (share, iterator);
		switch (atom->kind) {
		case NOLL_SHARE_IN: {
			//printf("Member case\n");
			if (noll_vector_size (atom->t_right) == 1) {
				if (noll_vector_at (atom->t_right,0)->kind == NOLL_STERM_SVAR) {
					fprintf(out_decl, "(assert ");
					if (!sign)
						fprintf(out_decl, "(not ");
					fprintf(out_decl, " (%s %s) ", noll_vector_at (svars,
							noll_vector_at (atom->t_right,0)->svar)->vname,
							noll_vector_at (lvars,atom->t_left->lvar)->vname);
					if (!sign)
						fprintf(out_decl, ")");
					fprintf(out_decl, ")\n");
				} else { //this case shouldn't arrive .. it is not handled in the boolean abstraction...it is equivalent to an equality
					fprintf(out_decl, "(assert ");
					if (!sign)
						fprintf(out_decl, "(not ");
					fprintf(out_decl, " (= (%s %s)) ",
							noll_vector_at (lvars, atom->t_left->lvar)->vname,
							noll_vector_at (lvars,
									noll_vector_at (atom->t_right,0)->lvar)->vname);
					if (!sign)
						fprintf(out_decl, ")");
					fprintf(out_decl, ")\n");
				}
			} else {
				fprintf(out_decl, "(assert ");
				if (!sign)
					fprintf(out_decl, "(not ");
				fprintf(out_decl, "(or ");
				for (uint_t i = 0; i < noll_vector_size(atom->t_right); i++) {
					if (noll_vector_at (atom->t_right,i)->kind
							== NOLL_STERM_SVAR) {
						fprintf(out_decl, " (%s %s) ", noll_vector_at (svars,
								noll_vector_at (atom->t_right,i)->svar)->vname,
								noll_vector_at (lvars,atom->t_left->lvar)->vname);
					} else {
						fprintf(out_decl, " (= (%s %s)) ",
								noll_vector_at (lvars,atom->t_left->lvar)->vname,
								noll_vector_at (lvars,
										noll_vector_at (atom->t_right,i)->lvar)->vname);
					}
				}
				fprintf(out_decl, ")");
				if (!sign)
					fprintf(out_decl, ")");
				fprintf(out_decl, ")\n");
			}
			break;
		}
		case NOLL_SHARE_NI: {
			//printf("Non-Member case\n");
			if (noll_vector_size (atom->t_right) == 1) {
				if (noll_vector_at (atom->t_right,0)->kind == NOLL_STERM_SVAR) {
					fprintf(out_decl, "(assert ");
					if (!sign)
						fprintf(out_decl, "(not ");
					fprintf(out_decl, " (not (%s %s)) ", noll_vector_at (svars,
							noll_vector_at (atom->t_right,0)->svar)->vname,
							noll_vector_at (lvars,atom->t_left->lvar)->vname);
					if (!sign)
						fprintf(out_decl, ")");
					fprintf(out_decl, ")\n");
				} else { //this case shouldn't arrive .. it is not handled in the boolean abstraction...it is equivalent to an equality
					fprintf(out_decl, "(assert ");
					if (!sign)
						fprintf(out_decl, "(not ");
					fprintf(out_decl, " (not (= (%s %s))) ",
							noll_vector_at (lvars,atom->t_left->lvar)->vname,
							noll_vector_at (lvars,
									noll_vector_at (atom->t_right,0)->lvar)->vname);
					if (!sign)
						fprintf(out_decl, ")");
					fprintf(out_decl, ")\n");
				}
			} else {
				fprintf(out_decl, "(assert ");
				if (!sign)
					fprintf(out_decl, "(not ");
				fprintf(out_decl, "(and ");
				for (uint_t i = 0; i < noll_vector_size(atom->t_right); i++) {
					if (noll_vector_at (atom->t_right,i)->kind
							== NOLL_STERM_SVAR) {
						fprintf(out_decl, " (not (%s %s)) ",
								noll_vector_at (svars,
										noll_vector_at (atom->t_right,i)->svar)->vname,
								noll_vector_at (lvars,atom->t_left->lvar)->vname);
					} else {
						fprintf(out_decl, " (not (= (%s %s))) ",
								noll_vector_at (lvars,atom->t_left->lvar)->vname,
								noll_vector_at (lvars,
										noll_vector_at (atom->t_right,i)->lvar)->vname);
					}
				}
				fprintf(out_decl, ")");
				if (!sign)
					fprintf(out_decl, ")");
				fprintf(out_decl, ")\n");
			}
			break;
		}
		case NOLL_SHARE_SUBSET: {
			if (noll_vector_size (atom->t_right) == 1) {
				fprintf(out_decl, "(assert ");
				if (!sign)
					fprintf(out_decl, "(not ");
				if (noll_vector_at (atom->t_right,0)->kind == NOLL_STERM_SVAR)
					fprintf(out_decl,
							"(forall ((?e addr)) (=> (%s ?e) (%s ?e)))",
							noll_vector_at (svars, atom->t_left->svar)->vname,
							noll_vector_at (svars,
									noll_vector_at (atom->t_right,0)->svar)->vname);
				else
					fprintf(out_decl,
							"(forall ((?e addr)) (=> (%s ?e) (= %s ?e)))",
							noll_vector_at (svars, atom->t_left->svar)->vname,
							noll_vector_at (lvars,
									noll_vector_at (atom->t_right,0)->lvar)->vname);
				if (!sign)
					fprintf(out_decl, ")");
				fprintf(out_decl, ")\n");
			} else {
				fprintf(out_decl, "(assert ");
				if (!sign)
					fprintf(out_decl, "(not ");
				fprintf(out_decl, "(forall ((?e addr)) (=> (%s ?e) (or ",
						noll_vector_at (svars, atom->t_left->svar)->vname);
				for (uint_t i = 0; i < noll_vector_size(atom->t_right); i++) {
					if (noll_vector_at (atom->t_right,0)->kind
							== NOLL_STERM_SVAR)
						fprintf(out_decl, " (%s ?e) ", noll_vector_at (svars,
								noll_vector_at (atom->t_right,i)->svar)->vname);
					else
						fprintf(out_decl, " (= %s ?e) ", noll_vector_at (lvars,
								noll_vector_at (atom->t_right,i)->lvar)->vname);
				}
				fprintf(out_decl, ") ) )");
				if (!sign)
					fprintf(out_decl, ")");
				fprintf(out_decl, ")\n");

			}
			break;
		}
		default: {
			break;
		}
		}
	}
	fclose(out_decl);
	return 1;
}

int noll_share_check(noll_var_array* lvars, noll_var_array* svars,
		noll_share_array* pos_share, noll_share_array* neg_share) {
	int isvalid = 0;
	FILE* out = fopen("sharing.smt", "w");
	fprintf(out, "\n");
	fclose(out);
	noll_share_check_euf_decl(lvars, svars, "sharing.smt");
	noll_share_check_euf_asserts(lvars, svars, pos_share, "sharing.smt", 1);
	noll_share_check_euf_asserts(lvars, svars, neg_share, "sharing.smt", 0);
	out = fopen("sharing.smt", "a");
	fprintf(out, "(check-sat)\n");
	fclose(out);

	char* command = (char*) malloc(100 * sizeof(char));
	memset(command, 0, 100 * sizeof(char));
	sprintf(command, "z3 -smt2 sharing.smt 1> smt.log");

	//call z3
	if (system(command) != -1) {
		FILE *res = fopen("smt.log", "r");
		char s[10];
		s[9] = '\0';
		fgets(s, 10, res);
		fclose(res);
		if (strcmp(s, "unsat\n") == 0) {
			printf("*******************UNSAT*******************\n");
			isvalid = 1;
		} else
			printf("*******************SAT*******************\n");
	}
	free(command);
	return isvalid;
}

/**
 * Normalize the formulae.
 * @return 1 if ok, 0 otherwise
 */
int noll_entl_normalize() {

	noll_form_t* pform = noll_entl_get_pform();
	noll_form_array* nform = noll_entl_get_nform();

	if (pform) {
		noll_prob->pabstr = NULL;
		if (tosat_old == true)
			normalize_incremental(pform, "p-out.txt");
		else
			noll_prob->pabstr = noll2sat_normalize(pform, "p-out.txt", true,
					false);
	}
#ifndef NDEBUG
	fprintf (stdout, "*** check-sat: normalized pform: \n");
	noll_form_fprint (stdout, noll_prob->pform);
	fprintf (stdout, "\n\n*** check-sat: normalize nform: \n");
	fflush (stdout);
#endif

	if (nform) {
		// store the computed boolean abstractions
		noll_prob->nabstr = noll_sat_array_new();
		noll_sat_array_resize(noll_prob->nabstr, noll_vector_size(nform));
		// go through negative formulae
		for (size_t i = 0; i < noll_vector_size(nform); i++) {
			noll_form_t* nform_i = noll_vector_at(nform,i);
			noll_sat_t* nform_i_abstr = NULL;
#ifndef NDEBUG
			fprintf (stdout, "\t\t(nform_%zu): begin normalize\n", i);
			fflush(stdout);
#endif
			if (tosat_old == true)
				normalize_incremental(nform_i, "n-out.txt");
			else
				nform_i_abstr = noll2sat_normalize(nform_i, "n-out.txt", true,
						false);
#ifndef NDEBUG
			fprintf (stdout, "\t\t(nform_%zu): end normalize\n", i);
			noll_form_fprint (stdout, nform_i);
			fflush(stdout);
#endif
			noll_vector_at(nform,i) = nform_i;
			noll_vector_at(noll_prob->nabstr,i) = nform_i_abstr;
		}
	}

#ifndef NDEBUG
	fprintf (stdout, "*** check-sat: END normalized formulae \n");
	noll_entl_fprint(stdout);
	fflush (stdout);
#endif
	return 1;
}

/**
 * Translate to graph representation all formulae in entailment
 * @return 1 if ok, 0 otherwise
 */
int noll_entl_to_graph(void) {

	noll_form_t* pform = noll_prob->pform;
	noll_form_array* nform = noll_entl_get_nform();

#ifndef NDEBUG
	fprintf (stdout, "*** check-sat: translate to graphs ...\n");
	for(uint_t i=0;i<pform->pure->size;i++)
	for(uint_t j=i+1;j <pform->pure->size;j++)
	if(noll_pure_matrix_at(pform->pure,i,j)==NOLL_PURE_EQ)
	printf("Variable %s equals %s\n",
			noll_vector_at(pform->lvars,i)->vname,
			noll_vector_at(pform->lvars,j)->vname);
#endif

	noll_prob->pgraph = noll_graph_of_form(pform);

#ifndef NDEBUG
	fprintf (stdout, "\n*****pos_graph: file dot_left_graph\n");
	noll_graph_fprint (stdout, noll_prob->pgraph);
//	noll_graph_fprint_dot ("dot_left_graph", pos_graph);
#endif

	if (nform) {
		// store the computed boolean abstractions
		noll_prob->ngraph = noll_graph_array_new();
		noll_graph_array_resize(noll_prob->ngraph, noll_vector_size(nform));
		// go through negative formulae
		for (size_t i = 0; i < noll_vector_size(nform); i++) {
			noll_form_t* nform_i = noll_vector_at(nform,i);
			noll_graph_t* nform_i_graph = noll_graph_of_form(nform_i);
			noll_vector_at(noll_prob->ngraph,i) = nform_i_graph;
#ifndef NDEBUG
			fprintf (stdout, "\n*****neg_graph: file dot_right_graph_%zu\n",i);
			char fname[20] = "\0";
			sprintf(fname, "dot_right_graph_%zu", i);
			noll_graph_fprint_dot (fname, nform_i_graph);
			fflush (stdout);
#endif
		}
	}
	return 1;
}

/**
 *  Build the homomorphism for this entailment problem
 *  @return 1 if h found, 0 otherwise
 */
int noll_entl_to_homomorphism(void) {

	int res = 1;
#ifndef NDEBUG
	fprintf (stdout, "*** check-sat: test homomorphism:\n");
#endif

	res = noll_graph_homomorphism(noll_vector_at(noll_prob->ngraph,0), // TODO: change for \/
			noll_prob->pgraph);

#ifndef NDEBUG
	fprintf (stdout, "*** check-sat: homomorphism found = \n");
	// TODO: print homomorphism found
#endif

	/*
	 * Check sharing constraints entailment for the found homomorphism
	 */
#ifndef NDEBUG
	fprintf (stdout, "*** check-sat: test sharing:\n");
	fprintf (stdout, "\n*****pos_graph: file dot_left_graph_compl\n");
	noll_graph_fprint (stdout, noll_prob->pgraph);
	noll_graph_fprint_dot ("dot_left_graph_compl", noll_prob->pgraph);
	fprintf (stdout, "\n*****neg_graph: file dot_right_graph_compl\n");
	//noll_graph_fprint_dot ("dot_right_graph_compl", noll_vector_at(nol_prob->ngraph,0));
	fflush (stdout);
#endif
// TODO: when updated share constraints in graphs
// do union of variables
// check_entl_sharing(pos_graph->lvars, pos_graph->svars,
// pos_graph->share,neg_graph->share);

	return 1;
}

/**
 * Check special cases for entailment.
 * @return 1 if satisfiable, 0 if unsat, -1 if not known
 */
int noll_entl_solve_special(void) {
// commented out becase noll_form_is_unsat() could not be found
//	if (((noll_prob->pform != NULL) && noll_form_is_unsat(noll_prob->pform))
//			|| ((noll_prob->nform != NULL)
//					&& noll_form_array_is_valid(noll_prob->nform))) {
//#ifndef NDEBUG
//		fprintf (stdout, "*** check-sat: special case 0 ...\n");
//#endif
//		return 0;
//	}
//
//	if ((noll_prob->pform != NULL) && noll_form_is_unsat(noll_prob->pform)
//			&& ((noll_prob->nform == NULL)
//					|| noll_form_array_is_unsat(noll_prob->nform))) {
//#ifndef NDEBUG
//		fprintf (stdout, "*** check-sat: special case 1 ...\n");
//#endif
//		return 1;
//	}
	if (((noll_prob->nform != NULL)
			&& (!noll_form_array_is_valid(noll_prob->nform))
			&& (noll_prob->pform == NULL))
			|| ((noll_prob->nform == NULL) && (noll_prob->pform == NULL)))
// equivalent to !pform || !nform
			{
#ifndef NDEBUG
		fprintf (stdout, "*** check-sat: special case 2 ...\n");
#endif
		return 1;
	}
	return -1;
}

/**
 * Check the nol_prob->cmd for the formula
 *    pform /\ not(\/ nform_i)
 * to obtain the result of the entailment
 *    pform ==> \/ nform_i
 *
 * @return 1 if satisfiable, 0 if not satisfiable
 */
int noll_entl_solve(void) {
	int res = 0;

#ifndef NDEBUG
	noll_entl_fprint(stdout);
	fflush(stdout);
#endif

	/*
	 * Test special cases, before normalizing the formulas
	 */
	res = noll_entl_solve_special();
	if (res != -1)
		return res;

#ifndef NDEBUG
	fprintf (stdout, "*** check-%ssat: not special case\n",
			(noll_prob->cmd == NOLL_FORM_SAT) ? "" : "un");
	fflush (stdout);
#endif

	/*
	 * Normalize both formulas (which also test satisfiability)
	 */
#ifndef NDEBUG
	fprintf (stdout, "*** check-%ssat: normalize\n",
			(noll_prob->cmd == NOLL_FORM_SAT) ? "" : "un");
#endif

	struct timeval tvBegin, tvEnd, tvDiff;

	gettimeofday(&tvBegin, NULL);

	noll_entl_normalize();

	/*
	 * Test the satisfiability of pform /\ not(\/_i nform)
	 */
	/*
	 * Special cases, not covered by graph homomorphism
	 */
	res = noll_entl_solve_special();
	if (res != -1)
		return res;

	/*
	 * If both formulas are not empty,
	 * translate formulas to graphs.
	 */
	res = noll_entl_to_graph();
	if (res == 0)
		goto check_end;

	/*
	 * Check graph homomorphism
	 */
// build homomorphism from right to left
	res = noll_entl_to_homomorphism();
// sharing constraints in pos_graph are updated and tested!
	if (!res)
		goto check_end;

	/*
	 * FIN
	 */
	check_end:

	gettimeofday(&tvEnd, NULL);
	time_difference(&tvDiff, &tvEnd, &tvBegin);
	printf("\nTotal time: %ld.%06ld\n\n", (long int) tvDiff.tv_sec,
			(long int) tvDiff.tv_usec);
	/*
	 * Free the allocated memory
	 * (only graphs, formulas will be deallocated at the end)
	 */
	noll_entl_free_aux();

	return res;
}
