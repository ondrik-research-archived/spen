# Makefile
#


include ../Makefile.config

#---------------------------------------
# Flags
#---------------------------------------

# Use ICFLAGS to specify machine-independent compilation flags.
ICFLAGS = -g -I. \
-I$(SMTLIB2_PREFIX)

ICXXFLAGS = -g \
-I$(LIBVATA_INCLUDE)

LDFLAGS = \
-L$(SMTLIB2_PREFIX) \
-L$(LIBVATA_LIB)

#DEBUG=_debug

#---------------------------------------
# Files
#---------------------------------------

CCINC = noll_vector.h \
	noll_types.h noll_vars.h noll_preds.h noll_form.h noll_graph.h \
	noll2bool.h noll2sat.h noll2graph.h \
	noll_graph2ta.h noll_pred2ta.h \
	noll_hom.h noll_entl.h \
	noll.h smtlib2noll.h \
	noll_ta_symbols.h \
	libvata_noll_iface.h

CCSRC = noll_types.c \
	noll_vars.c \
	noll_preds.c noll_form.c \
	noll_graph.c \
	noll2bool.c noll2sat.c noll2graph.c \
	noll_graph2ta.c noll_pred2ta.c \
	noll_hom.c noll_entl.c \
	noll.c smtlib2noll.c \
	noll_ta_symbols.c \
	noll-dp.c 

CXXSRC = libvata_noll_iface.cc

#---------------------------------------
# Rules
#---------------------------------------

SHARED_LIBS = -lsmtlib2parser \
	-lm \
	-lvata

all: spen

#	$(CXX) $(CXXFLAGS) -o $@ $^ \

spen: $(subst .c,$(DEBUG).o,$(CCSRC)) $(subst .cc,$(DEBUG).o,$(CXXSRC))
	$(CXX) -o $@ $^ \
	$(LDFLAGS) \
	$(SHARED_LIBS)

clean:
	rm -f *.o *~ *-out.txt *.dot result.txt
	
distclean: clean
	rm spen

install: spen
	mv spen $(HOME)/bin

indent: $(CCINC) $(CCSRC) 
	indent -nut $^

#---------------------------------------
# IMPLICIT RULES AND DEPENDENCIES
#---------------------------------------

.SUFFIXES: .c .h .a .o .so .cc

libvata_noll_iface.o: libvata_noll_iface.cc $(CCINC) $(DEPS)
	$(CXX) $(CXXFLAGS) $(ICXXFLAGS) -c -o $@ $<

libvata_noll_iface_debug.o: libvata_noll_iface.cc $(CCINC) $(DEPS)
	$(CXX) $(CXXFLAGS_DEBUG) $(ICXXFLAGS) -c -o $@ $<

%.o: %.c $(CCINC) $(DEPS)
	$(CC) $(CFLAGS) $(ICFLAGS) -c -o $@ $<

%_debug.o: %.c $(CCINC) $(DEPS)
	$(CC) $(CFLAGS_DEBUG) $(ICFLAGS) -c -o $@ $<


