cmake_minimum_required(VERSION 2.8.2)

set(CMAKE_COLOR_MAKEFILE ON)
# set(CMAKE_VERBOSE_MAKEFILE ON)

add_compile_options($<$<COMPILE_LANGUAGE:CXX>:-std=c++11> $<$<COMPILE_LANGUAGE:C>:-std=gnu99>)

# uncomment for profiling
#add_definitions(-pg)
#set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -pg")

include_directories(../libvata/include)
include_directories(../smtlib2parser-1.4)

add_executable(spen
	libvata_noll_iface.cc
	noll-dp.c
	noll.c
	noll2bool.c
	noll2graph.c
	noll2sat.c
	noll_entl.c
	noll_form.c
	noll_graph.c
	noll_graph2ta.c
	noll_hom.c
	noll_lemma.c
	noll_norm.c
	noll_option.c
	noll_pred2ta.c
	noll_pred2ta_gen.c
	noll_preds.c
	noll_sat.c
	noll_ta_symbols.c
	noll_tree.c
	noll_types.c
	noll_vars.c
	smtlib2noll.c
)

find_library(LIBVATA NAMES libvata.a PATHS ../libvata/build/src)
target_link_libraries(spen ${LIBVATA})
target_link_libraries(spen smtlib2parser)
