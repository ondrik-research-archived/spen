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

#ifndef _NOLL_PREDS_H_
#define	_NOLL_PREDS_H_

#ifdef	__cplusplus
extern "C"
{
#endif

#include "noll_types.h"
#include "noll_vars.h"
#include "noll_form.h"

  /* ====================================================================== */
  /* Datatypes */
  /* ====================================================================== */

  /** Predicate definition
   */
  typedef struct noll_pred_binding_t
  {
    size_t pargs;               // type of list = number of arguments of this record type 2 or 4
    noll_var_array *vars;       // nil + formal arguments + local variables
    uint_t fargs;               // number of formal arguments in the array above
    noll_space_t *sigma_0;      // points-to part
    noll_space_t *sigma_1;      // nested part
  } noll_pred_binding_t;

  /** Predicate typing infos
   */
  typedef struct noll_pred_typing_t
  {
    /* typing record for this predicate, index in record_array
     */
    uid_t ptype0;
    /* array of size @global records_array 
     * with 1 for records covered by pred
     */
    noll_uint_array *ptypes;
    /* array of size @global fields_array 
     * with values of @type noll_pfld_t for each field used in pred
     */
    noll_uint_array *pfields;
    bool useNil;                /* the predicate use fields to nil */
    bool isTwoDir;              /* the predicate is a two direction */
    /* array of size @global preds_array
     * with values 1 for predicates called inside the definition of pred
     */
    noll_uint_array *ppreds;
  } noll_pred_typing_t;

  /** Predicate information:
   * - the name of the predicate
   * - the type(s) of the variable
   */
  typedef struct noll_pred_t
  {
    char *pname;                // declaration name
    uid_t pid;                  // predicate identifier
    noll_pred_binding_t *def;   // predicate definition
    noll_pred_typing_t *typ;    // predicate typing infos
  } noll_pred_t;

  /** Type of the global array of predicates. */
    NOLL_VECTOR_DECLARE (noll_pred_array, noll_pred_t *);

  /* ====================================================================== */
  /* Globals */
  /* ====================================================================== */

  extern noll_pred_array *preds_array;  // predicates

  void noll_pred_init (void);
  /* Initialize global arrays of predicates */

  /* ====================================================================== */
  /* Other methods */
  /* ====================================================================== */

  uid_t noll_pred_array_find (const char *name);
  /* Returns the id of the predicate in preds_array */

  uid_t noll_pred_register (const char *pname, noll_pred_binding_t * def);
  /* Insert the predicate definition in the global array */

  uid_t noll_pred_typecheck_call (uid_t pid, uid_t * actuals_ty, uid_t size);
  /* Typecheck the call of name with the types of parameters given in
   * actuals_ty of length size.
   */

        /**
	 * @brief  Returns the predicate with given Predicate ID
	 *
	 * @param[in]  pid   ID of the desired predicate
	 *
	 * @returns  The desired predicate
	 */
  const noll_pred_t *noll_pred_getpred (uid_t pid);

  const char *noll_pred_name (uid_t pid);
  /* Accessors */

  bool noll_pred_order_lt (uid_t lhs, uid_t rhs);
  /* Total ordering of predicates using their call */

  bool noll_pred_use_nil (uid_t pid);
  /* Retrun true if pid uses nil internally */

  bool noll_pred_is_one_dir (uid_t pid);
  /* Retrun true if pid is a one direction predicate */
  /* WARNING: for the moment, only dll are two direction predicates */

  bool noll_pred_is_field (uid_t pid, uid_t fid, noll_field_e kind);
  /* Search the field in the predicate with a role of at most kind.
   */

  bool noll_pred_is_backbone_field (uid_t fid);
  /* Test if fid is a backbone for some predicate */

        /**
	 * @brief  Checks whether the field as the main backbone field of a predicate
	 *
	 * Checks whether @p fid denoters the main backbone firld of some predicate.
	 * That is, the least backbone field (w.r.t. the field ordering) that goes to
	 * @p X_tl.
	 *
	 * @param[in]  fid  The field identifier
	 *
	 * @returns  @p true iff @p fid denotes the main backbone field of some
	 *           predicate, @p false otherwise
	 */
  bool noll_pred_is_main_backbone_field (uid_t fid);


  int noll_pred_type (void);
  /* Type the predicate definitions.
   */

        /**
	 * @brief  Retrieves the minimum field of a predicate
	 *
	 * @param[in]  pid  ID of the predicate
	 *
	 * @returns  The minimum field of the predicate with the ID @p pid
	 */
  uid_t noll_pred_get_minfield (uid_t pid);

  int noll_field_order (void);
  /* Order the fields using the predicate order.
   */

  /* ====================================================================== */
  /* Printing */
  /* ====================================================================== */

  void noll_pred_array_fprint (FILE * f, noll_pred_array * a,
                               const char *msg);
  /* Print the array a. */


#ifdef	__cplusplus
}
#endif

#endif                          /* _NOL_PREDS_H_ */
