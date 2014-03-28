********************************************************************************
*                                                                              *
*                                     SPEN                                     *
*                                                                              *
*                         (SeParation logic ENtailment)                        *
*                                                                              *
*                           SAS'14 Artifact Submission                         *
*                                                                              *
********************************************************************************


About
=====

SPEN is an implementation of the decision procedure for entailment problems
between formulas in the fragment of Separation Logic with Recursive Definitions
(SLRD) defined in [paper#13].
See also the technical report for a detailed presentation at [FIT-TR-2014-01]
(http://www.fit.vutbr.cz/~ilengal/pub/FIT-TR-2014-01.pdf).


How to use 
==========

Before executing, please check that your environment variables are 
correctly set, i.e.:

  > echo $PATH
  $HOME/bin

  > echo $LD_LIBRARY_PATH
  $HOME/lib


The benchmark suites given in the paper are available in the directory

  $HOME/spen/samples/

in the directories

  smt-PLDI11   the benchmark suite on singly linked lists
               used in [NavaroPerezRybalchenko-PLDI'11]

  dll          the benchmark suite for doubly linked lists

  nll          the benchmark suite for nested linked lists

  nlcl         the benchmark suite for nested cyclic linked lists

  skl2         the benchmark suite for skip lists of level 2

  skl3         the benchmark suite for skip lists of level 3


To run SPEN on these examples, you either execute one example, e.g.,

  > cd $HOME/spen/samples
  > spen nll/nll-vc01.smt

or you run a full benchmark suite by running, e.g.,

  > ./doall.sh nll

or, only for the smt-PLDI11 suite, you execute, e.g.,

  > cd $HOME/spen/samples/smt-PLDI2011
  > ./doall.sh clone
  > ./doall.sh spaguetti
  > ./doall.sh smallfoot
  > ./doall.sh bolognesa


Limitations of the tool
=======================

SPEN is a prototype tool intented for the evaluation of the principles described
in [paper#13]. It is very likely that it contains bugs and running it on test
cases other than those provided in the benchmark directory may result in program
crashes. The currently supported set of inductive predicates is limited to those
given in the benchmark directory.
