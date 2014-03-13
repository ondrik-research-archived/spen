# Makefile
#

TOOL=../../src/nolldp-test
OPTION=-n

clean:
	rm -f *out.txt result.txt *.dot

purge: clean
	rm -f *.log *.res

#---------------------------------------
# IMPLICIT RULES AND DEPENDENCIES
#---------------------------------------

.SUFFIXES: .smt .log 


%.log: %.smt
	$(TOOL) $(OPTION) $< &> $@
