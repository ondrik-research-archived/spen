
About
=====
This is a decision procedure for entailment problems between formulas in
the fragment of Separation Logic with Recursive Definitions (SLRD) 
defined in [paper#13].
See also the technical report for a detailed presentation at [FIT-TR-2014-01].


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

	smt-PLDI11	the benchmark suite on singly linked lists
			used in [NavaroPerezRybalchenko-PLDI'11]

	dll		the benchmark suite on doubly linked lists

	nll		the benchmark suite on nested linked lists

	nlcl		the benchmark suite on nested cyclic linked lists

	skl3		the benchmark suite on skip lists of level 3


To run 'spen' on these examples, you either execute one example, e.g.,

> spen nll/nll-vc01.smt


or you run a full benchmark suite, e.g.,

> ./doall.sh nll


or, only for the smt-PLDI11 suite you execute, e.g.,

> ./doall.sh smt-PLDI11 clone
