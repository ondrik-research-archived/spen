# Makefile
#


include Makefile.config

#---------------------------------------
# Flags
#---------------------------------------

# Use ICFLAGS to specify machine-independent compilation flags.
ICFLAGS = -g -I. \
-I$(SMTLIB2_PREFIX)

LDFLAGS = \
-L$(SMTLIB2_PREFIX)

#---------------------------------------
# Files
#---------------------------------------

CCINC = noll_vector.h \
	noll_types.h noll_vars.h noll_preds.h noll_form.h noll_graph.h \
	noll2bool.h noll2sat.h noll2graph.h \
	noll_graph2ta.h noll_pred2ta.h \
	noll_hom.h noll_entl.h \
	noll.h smtlib2noll.h 

CCSRC = noll_types.c \
	noll_vars.c \
	noll_preds.c noll_form.c \
	noll_graph.c \
	noll2bool.c noll2sat.c noll2graph.c \
	noll_graph2ta.c noll_pred2ta.c \
	noll_hom.c noll_entl.c \
	noll.c smtlib2noll.c \
	noll-dp.c 

#---------------------------------------
# Rules
#---------------------------------------

#TODO
SHARED_LIBS = -lsmtlib2parser \
	-lm 

all: nolldp

nolldp: $(subst .c,$(DEBUG).o,$(CCSRC))
	$(CC) $(CFLAGS_DEBUG) $(ICFLAGS) -o $@ $^ \
	$(LDFLAGS) \
	$(SHARED_LIBS)

clean:
	rm -f *.o *~ *-out.txt result.txt
	
distclean: clean
	rm nolldp

#---------------------------------------
# IMPLICIT RULES AND DEPENDENCIES
#---------------------------------------

.SUFFIXES: .c .h .a .o .so


%.o: %.c $(CCINC) $(DEPS)
	$(CC) $(CFLAGS) $(ICFLAGS) -c -o $@ $<

%_debug.o: %.c $(CCINC) $(DEPS)
	$(CC) $(CFLAGS_DEBUG) $(ICFLAGS) -c -o $@ $<


