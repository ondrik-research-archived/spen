# Makefile
#

TOOL=../../src/spen
OPTION=

.PHONY: clean purge

clean:
	rm -f *out.txt result.txt graph-*.txt form-*.txt *.dot gmon.out

purge: clean
	rm -f *.log

#---------------------------------------
# IMPLICIT RULES AND DEPENDENCIES
#---------------------------------------

.SUFFIXES: .smt .log 


%.smt.log: %.smt
	$(TOOL) $(OPTION) $< > $@ 2>&1
