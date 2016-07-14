cmake_minimum_required(VERSION 2.8.2)


# 3rd party modules
set(CMAKE_MODULE_PATH "${CMAKE_SOURCE_DIR}/cmake/Modules/")
# Enable fancy colours
set(CMAKE_COLOR_MAKEFILE ON)
# Enable verbose output for 'make'
# set(CMAKE_VERBOSE_MAKEFILE ON)


##############################################################################
#                             OUTPUT CUSTOMIZATION
##############################################################################

# Building with debug information even in release (use e.g. for profiling with Callgrind)
option(DEBUG_INFO_FOR_RELEASE "build with debug info even in release builds" OFF)

##############################################################################
#                               COMPILER FUN
##############################################################################

# enable C++
enable_language(CXX)

# set(REQUIRED_GCC_VERSION 4.8.0)
# set(GCC_ALTERNATIVES g++ g++-4.8)

# get the git revision
include(GetGitRevisionDescription)
git_describe(GIT_DESCRIBE)
get_git_head_revision(GIT_REFSPEC GIT_SHA1)


##############################################################################
#                     TESTING FEATURES OF THE COMPILER
##############################################################################

# You can force the GCC version here
#set(CMAKE_C_COMPILER "gcc-4.8")
#set(CMAKE_CXX_COMPILER "g++-4.8")

# Debug information for release builds
if (DEBUG_INFO_FOR_RELEASE)
	set(CMAKE_C_FLAGS_RELEASE  "${CMAKE_C_FLAGS_RELEASE} -g")
	set(CMAKE_CXX_FLAGS_RELEASE "${CMAKE_CXX_FLAGS_RELEASE} -g")
	message("-- Enabling debug information for RELEASE builds")
endif()

##############################################################################
#                                 PROJECT
##############################################################################

project(spen)

# Include CTest so that sophisticated testing can be done now
include(CTest)


##############################################################################
#                                DEPENDENCIES
##############################################################################

# Necessary packages
find_package(FLEX 2.5.33 REQUIRED)
find_package(BISON 2.4.1 REQUIRED)


##############################################################################
#                                SUB-MODULES
##############################################################################

# Process subdirectories
add_subdirectory(libvata)
add_subdirectory(smtlib2parser-1.4)
add_subdirectory(src)
