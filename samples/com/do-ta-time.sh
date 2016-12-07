#!/bin/bash

# Version with less as possible use of the system

PRED=$1

PROC=$2

SHARED_MAKE="make -f ../Makefile"

cd ${PRED}

# for i in `ls ${PRED}${PROC}*-vc??.smt`
for i in `ls *.smt`
do
        BN_FILE=`basename -s .smt ${i}`
	LOG_FILE="${i}.log"

	${SHARED_MAKE} --always-make ${LOG_FILE}
	${SHARED_MAKE} --quiet clean
done

