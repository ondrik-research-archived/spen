[The patch for unsatcore is compatible with the patch for incremental ]

To obtain unsat proof for minisat:

export MROOT=<minisat-dir>

cd core

patch -p1 < minisat-2.2.0-for-unsat.patch

make r

mv minisat_release minisat_unsat

