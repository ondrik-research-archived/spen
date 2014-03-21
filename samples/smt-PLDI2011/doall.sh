#!/bin/sh

P=$1
for i in `ls $P*.smt` 
do 
	echo "==== $i"
        f=`basename -s ".smt" $i`
	echo "==== $f"
	make $f.log
	tail -3 $f.log > $f.res
	diff base.exp $f.res
	make clean
        rm $f.res
done

