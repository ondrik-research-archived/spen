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
 * Options for the decision procedure.
 */

#include "noll_option.h"
#include <string.h>


/* ====================================================================== */
/* Boolean abstraction */
/* ====================================================================== */

bool tosat_old = false;

void
noll_option_set_tosat (int version)
{
  if (version != 0)
    tosat_old = false;
  else
    tosat_old = true;
}

bool
noll_option_is_tosat (int version)
{
  if (version == 0)
    return tosat_old;
  else
    return !(tosat_old);
}


/* ====================================================================== */
/* Translation of predicates to tree automata. */
/* ====================================================================== */

bool preds_builtin = false;

void
noll_option_set_preds (bool isbuiltin)
{
  preds_builtin = isbuiltin;
}

bool
noll_option_is_preds_builtin (void)
{
  return preds_builtin;
}

int pred_ls_check = 1;

void
noll_option_set_checkLS (int version)
{
  pred_ls_check = (version == 0) ? 0 : 1;
}

bool
noll_option_is_checkLS (int version)
{
  if (pred_ls_check == 0)
    return (version == 0) ? true : false;
  else
    return (version != 0) ? true : false;
}

bool pred2ta_opt = false;

void
noll_option_set_pred2ta_opt (void)
{
  pred2ta_opt = true;
}

bool
noll_option_is_pred2ta_opt (void)
{
  return pred2ta_opt;
}

void
noll_option_set (char *option)
{
  if (strcmp (option, "-n") == 0)
    {
      noll_option_set_tosat (0);        /* set old version */
      return;
    }
  if (strcmp (option, "-b") == 0)
    {
      noll_option_set_preds (true);     /* builtin predicates */
      return;
    }
  if (strcmp (option, "-o1") == 0)
    {
      noll_option_set_checkLS (0);      /* special check for LS edges */
      return;
    }
  if (strcmp (option, "-o2") == 0)
    {
      noll_option_set_pred2ta_opt ();   /* optimized check for predicate edges */
      return;
    }
  if (strcmp (option, "-o") == 0)
    {
      noll_option_set_checkLS (0);      /* apply all optimizations */
      noll_option_set_pred2ta_opt ();
      return;
    }
  printf ("Unknown option: %s! ignore.\n", option);
}


void
noll_option_print (FILE * f)
{

  fprintf (f, "\t-n:     internal switch to old normalisation procedure\n");
  fprintf (f,
           "\t-b:     use predefined recursive definitions (set from name)\n");
  fprintf (f, "\t-o:     apply all optimizations\n");
  fprintf (f, "\t-o1:    optimized check of LS edges\n");
  fprintf (f, "\t-o2:    optimized construction of tree automata\n");

}
