# Makefile
#

TOOL=../../src/nolldp
OPTION=-n

clean:
	rm *out.txt result.txt

purge: clean
	rm *.log

#---------------------------------------
# IMPLICIT RULES AND DEPENDENCIES
#---------------------------------------

.SUFFIXES: .smt .log 


%.log: %.smt
	$(TOOL) $(OPTION) $< &> $@
