#!/bin/sh

if [ "$#" -ne 1 ]; then
	echo "usage: $0 <predicate>"
	exit 1
fi

P=$1

for i in `ls $P/$P-vc??.smt` 
do 
	echo "==== $i"
        f=`basename -s ".smt" $i`
	echo "==== $f"
	make $P/$f.log
	tail -3 $P/$f.log > $P/$f.res
	diff $P/$f.smt.exp $P/$f.res
	make clean
        rm $P/$f.res
done

