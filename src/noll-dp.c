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

#include <stdio.h>
#include "smtlib2noll.h"
#include "noll_ta_symbols.h"

/* ====================================================================== */
/* MAIN/Main/main */
/* ====================================================================== */

/**
 * Set options declared in different files
 */
void
noll_set_option (char *option)
{
  if (strcmp (option, "-satold") == 0)
    {
      tosat_old = true;
      return;
    }
  printf ("Unknown option: %s! ignore.\n", option);
}

/**
 * Print informations on usage.
 */
void
print_help (void)
{
  printf ("spen: decision procedure for SLRD, version 0.1\n");
  printf ("Usage: spen <file>\n");
  printf ("\t<file>: input file in the SMTLIB2 format\n");
  printf
    ("See http://www.liafa.univ-paris-diderot.fr/spen for more details.\n");
}

/**
 * Entry of the decision procedure.
 * @requires: only one problem per file
 *
 * Call: noll-dp [-n] file.smt2
 */
int
main (int argc, char **argv)
{
  // Step 0: Check the arguments
  if (argc <= 1)
    {
      print_help ();
      return 1;
    }
  int arg_file = 1;
  if (argc >= 3)
    {
      arg_file = argc - 1;
      for (int i = 1; i < arg_file; i++)
	noll_set_option (argv[i]);
    }

  // Step 1: Parse the file and initialize the problem
  // pre: the file shall exists.
  FILE *f = fopen (argv[arg_file], "r");
  if (!f)
    {
      printf ("File %s not found!\nquit.", argv[arg_file]);
      return 1;
    }

  // initialize the TA symbol database
  noll_ta_symbol_init ();

  // initialize the problem
  noll_entl_init ();
  noll_entl_set_fname (argv[arg_file]);
  // call the parser
  smtlib2_noll_parser *sp = smtlib2_noll_parser_new ();
  smtlib2_abstract_parser_parse ((smtlib2_abstract_parser *) sp, f);

  // Step 2: call the solving execute the commands in the file (check-sat)
  // done in (noll.c) noll_check
  // also sets the smtlib2 parser result

  // Step 3: finish (free memory, etc.)
  smtlib2_noll_parser_delete (sp);
  fclose (f);
  noll_entl_free ();
  noll_ta_symbol_destroy ();	// destroy the TA symbol database

  return 0;
}
