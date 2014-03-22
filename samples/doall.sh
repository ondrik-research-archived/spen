#!/bin/sh

if [ "$#" -ne 1 ]; then
	echo "usage: $0 <predicate>"
	exit 1
fi

PRED=$1

SHARED_MAKE="make -f ../Makefile"

cd ${PRED}
echo "========================== Testing predicate \"${PRED}\" =========================="

for i in `ls ${PRED}-vc??.smt`
do
	LOG_FILE="${i}.log"
	RESULT_FILE="${i}.res"
	EXPECTED_FILE="${i}.exp"

	echo "==== Testing file \"${i}\""
	${SHARED_MAKE} --always-make ${LOG_FILE}
	if [ $? -ne "0" ] ; then
		echo "INTERNAL ERROR"
		echo "result for ${i}:                                              \033[1;33mFAILED\033[0m"
		continue
	fi
	tail -1 ${LOG_FILE} > ${RESULT_FILE}
	RUN_TIME=$(grep "Total time" ${LOG_FILE} | sed 's/^.*:\(.*\)$/\1/')
	diff ${EXPECTED_FILE} ${RESULT_FILE} >/dev/null
	if [ $? -ne "0" ] ; then
		echo "==== received \"$(cat ${RESULT_FILE})\" while expecting \"$(cat ${EXPECTED_FILE})\""
		echo "result for ${i}:                                              \033[1;31mERROR\033[0m"
	else
		echo "==== received expected result:    $(cat ${RESULT_FILE})"
		echo "result for ${i}:                                              \033[1;32mOK\033[0m       in time ${RUN_TIME} sec"
	fi
	${SHARED_MAKE} --quiet clean
	rm ${RESULT_FILE}
done

