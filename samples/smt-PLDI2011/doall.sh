#!/bin/sh

for i in `ls *.smt` 
do 
	echo "==== $i"
        f=`basename -s ".smt" $i`
	echo "==== $f"
	make $f.log
	tail -3 $f.log > $f.res
	diff $i.exp $f.res
	make clean
        rm $f.res
done

