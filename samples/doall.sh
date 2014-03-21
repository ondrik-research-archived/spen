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
	make $f.log
	tail -3 $f.log > $f.res
	diff $P/$i.exp $f.res
	make clean
        rm $f.res
done

