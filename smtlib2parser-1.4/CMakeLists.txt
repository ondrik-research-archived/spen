cmake_minimum_required(VERSION 2.8.2)

set(CMAKE_COLOR_MAKEFILE ON)
# set(CMAKE_VERBOSE_MAKEFILE ON)

add_compile_options(-static)
add_compile_options(-std=c99)
add_compile_options(-pedantic)
add_compile_options(-g)
add_compile_options(-Wall)
add_compile_options(-fPIC)

# uncomment for profiling
#add_definitions(-pg)
#set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -pg")

flex_target(smtlib2flex smtlib2flexlexer.l ${CMAKE_CURRENT_BINARY_DIR}/smtlib2flexlexer.c COMPILE_FLAGS "--header-file=${CMAKE_CURRENT_BINARY_DIR}/smtlib2flexlexer.h")
bison_target(smtlib2bison  smtlib2bisonparser.orig.y ${CMAKE_CURRENT_BINARY_DIR}/smtlib2bisonparser.c)
add_flex_bison_dependency(smtlib2flex smtlib2bison)

include_directories(.)
include_directories(${CMAKE_CURRENT_BINARY_DIR})


add_library(smtlib2parser
	smtlib2abstractparser.c
	smtlib2bisonparser.c
	smtlib2charbuf.c
	smtlib2flexlexer.c
	smtlib2hashtable.c
	smtlib2parser.h
	smtlib2scanner.c
	smtlib2stream.c
	smtlib2termparser.c
	smtlib2utils.c
	smtlib2vector.c
)
