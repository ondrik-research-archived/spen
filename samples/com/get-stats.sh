#!/bin/bash

for i in `ls *$1-vc*.slog`
do
	BNAME=`basename -s .slog ${i}`
	echo "---- file ${BNAME}"
	NRULEB=`grep "spen: match the base rule" ${i} | wc -l`
	echo "base-rule: ${NRULEB}"
	NRULER=`grep "spen: match the recursive rule" ${i} | wc -l`
	echo "rec-rule: ${NRULER}"
	NEDGER=`grep "spen: match the atom" ${i} | wc -l`
	echo "edge-match: ${NEDGER}"
	NLEMMACPO=`grep "lemma COMPOSITION" ${i} | wc -l`
	echo "lemma COMP: ${NLEMMACPO}"
	NLEMMACPL=`grep "lemma COMPLETION" ${i} | wc -l`
	echo "lemma CMPL: ${NLEMMACPL}"
	NLEMMAINS=`grep "lemma INST" ${i} | wc -l`
	echo "lemma INST: ${NLEMMAINS}"
done


echo "===== Summary"
FNAME=*.slog

NRULEB=`grep "spen: match the base rule" ${FNAME} | wc -l`
echo "base-rule: ${NRULEB}"
NRULER=`grep "spen: match the recursive rule" ${FNAME} | wc -l`
echo "rec-rule: ${NRULER}"
NEDGER=`grep "spen: match the atom" ${FNAME} | wc -l`
echo "edge-match: ${NEDGER}"
NLEMMACPO=`grep "lemma COMPOSITION" ${FNAME} | wc -l`
echo "lemma COMP: ${NLEMMACPO}"
NLEMMACPL=`grep "lemma COMPLETION" ${FNAME} | wc -l`
echo "lemma CMPL: ${NLEMMACPL}"
NLEMMAINS=`grep "lemma INST" ${FNAME} | wc -l`
echo "lemma INST: ${NLEMMAINS}"

