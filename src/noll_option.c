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

int pred2ta_opt = 0;

void
noll_option_set_pred2ta_opt (int level)
{
  pred2ta_opt = (level > 0) ? level : 0;
}

int
noll_option_get_pred2ta_opt (void)
{
  return pred2ta_opt;
}


/* ====================================================================== */
/* Verbosity. */
/* ====================================================================== */

bool print_diagnosis = false;

void
noll_option_set_diag (void)
{
  print_diagnosis = true;
}

bool
noll_option_is_diag (void)
{
  return print_diagnosis;
}


int verbosity_level = 0;

void
noll_option_set_verb (int level)
{
  verbosity_level = (level > 0) ? level : 0;
}

int
noll_option_get_verb (void)
{
  return verbosity_level;
}


/* ====================================================================== */
/* Set/Print. */
/* ====================================================================== */

int
noll_option_set (char *option)
{
  if (strcmp (option, "-b") == 0)
    {
      noll_option_set_preds (true);     /* NYI: builtin predicates */
      return 1;
    }
  if (strcmp (option, "-d") == 0)
    {
      noll_option_set_diag ();  /* set diagnosis */
      return 1;
    }
  if (strcmp (option, "-n") == 0)
    {
      noll_option_set_tosat (0);        /* use old version of boolean abstraction */
      return 1;
    }
  if (strcmp (option, "-o1") == 0)
    {
      noll_option_set_checkLS (0);      /* NYI: special check for LS edges */
      return 1;
    }
  if (strcmp (option, "-o2") == 0)
    {
      noll_option_set_pred2ta_opt (1);  /* NYI: optimized check for predicate edges */
      return 1;
    }
  if (strcmp (option, "-o") == 0)
    {
      noll_option_set_checkLS (0);      /* NYI: apply all optimizations */
      noll_option_set_pred2ta_opt (1);
      return 1;
    }
  if (strcmp (option, "-v") == 0)
    {
      noll_option_set_verb (1); /* verbosity level */
      return 1;
    }
  if (option != NULL && option[0] == '-')
    {
      printf ("Unknown option: %s! ignore.\n", option);
      return -1;
    }
  return 0;
}


void
noll_option_print (FILE * f)
{

  fprintf (f, "Options:\n");
  fprintf (f,
           "  -b     use predefined recursive definitions (set from name)\n");
  fprintf (f, "  -d     print diagnosis messages\n");
  fprintf (f, "  -n     internal switch to old normalisation procedure\n");
  fprintf (f, "  -o     apply all optimizations\n");
  fprintf (f, "  -o1    optimized check of LS edges\n");
  fprintf (f, "  -o2    optimized construction of tree automata\n");

}
