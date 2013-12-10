To obtain incremental minisat:

export MROOT=<minisat-dir>

cd core

patch < minisat-2.2.0-for-icnf.patch

make r

mv minisat_release minisat_inc

