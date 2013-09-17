About
=====
This is a decision procedure for NOLL logic.

Requires
========
To compile:

- a C99 compiler (tested under gcc)

- GNU flex >= 2.5.33

- GNU bison (tested under bison 2.4.1)

- SMTLIB2 parser of Alberto Griggio available at 
  https://es.fbk.eu/people/griggio/misc/smtlib2parser.html


To execute:
- MINISAT solver available at
  http://minisat.se/
  and compiled with the incremental feature (see README_incremental_minisat.txt)


Installation
============
1) Configuring: 
   - change the SMTLIB2_PREFIX variable in the Makefile.config file
     with the directory where can be found the libsmtlib2parser.so

   - (optional)
     change the compiler name or the compilation flags for the C compiler


2) Compiling:
   - do 'make' in src directory


3) Install:
   - put the 'minisat' tool in the PATH
   - move the 'nolldp' binary to a known executable path


