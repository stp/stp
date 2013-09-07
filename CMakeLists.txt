project(STP)
cmake_minimum_required(VERSION 2.6 FATAL_ERROR)

# Search paths for custom CMake modules
set(CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/cmake/modules)

# -----------------------------------------------------------------------------
# Make RelWithDebInfo the default build type if otherwise not set
# -----------------------------------------------------------------------------

if(DEFINED CMAKE_BUILD_TYPE)
  set(CMAKE_BUILD_TYPE ${CMAKE_BUILD_TYPE}
  CACHE STRING "Choose the type of build: None(CMAKE_CXX_FLAGS or CMAKE_C_FLAGS used) Debug Release RelWithDebInfo MinSizeRel.")
else()
  set(CMAKE_BUILD_TYPE RelWithDebInfo CACHE STRING
  "Choose the type of build, options are: None(CMAKE_CXX_FLAGS or CMAKE_C_FLAGS used) Debug Release RelWithDebInfo MinSizeRel.")
endif()

# -----------------------------------------------------------------------------
# Determine the locations of C++ hash_set and hash_map
# -----------------------------------------------------------------------------

include(CheckCxxHashSet)
check_cxx_hashset()

include(CheckCxxHashMultiSet)
check_cxx_hashmultiset()

include(CheckCxxHashMap)
check_cxx_hashmap()

# -----------------------------------------------------------------------------
# Set the appropriate build flags
# -----------------------------------------------------------------------------

set(CMAKE_CXX_FLAGS_RELWITHDEBINFO "-Wno-deprecated -D __STDC_LIMIT_MACROS -D __STDC_FORMAT_MACROS -O1 -mtune=native")
#        "-std=c++0x -pedantic -Wall -Wextra -Wunused -Wsign-compare -Wtype-limits -Wuninitialized -Wno-deprecated -g -fno-omit-frame-pointer -O4 -mtune=native")
set(CMAKE_CXX_FLAGS_DEBUG "-std=c++0x -Wunused -Wsign-compare -Wtype-limits -Wuninitialized -Wall -Wno-deprecated -O0 -ggdb")
set(CMAKE_CXX_FLAGS_RELEASE "-std=c++0x -O2 -g -DNDEBUG -mtune=native")


if(WIN32)
  # build shared lib on windows is not prepared at source level
  set(BUILD_SHARED_LIB OFF)
  set(FLEX_PATH_HINT "e:/cygwin/bin" CACHE STRING "Flex path hints, can be null if on your path")
  set(FLEX_PATH_HINT "e:/cygwin/bin" CACHE STRING "Bison path hints, can be null if on your path")
  set(FLEX_PATH_HINT "C:/Perl/bin" CACHE STRING "Perl path hints, can be null if on your pat")

  set(PHINTS ${PERL_PATH_HINT} ${FLEX_PATH_HINT} ${BISON_PATH_HINT})

  if(MSVC)
      set(OPTIMIZITION_FLAGS  "/GL /Ox /Oi /Ot /Oy")
      set(STP_DEFS_COMM ${STP_DEFS_COMM} -D_CRT_SECURE_NO_WARNINGS)
      set(STP_INCL_COMM ../winports ../winports/msc99hdr ${STP_INCL_COMM})

      # stack size of MSVC must be specified
      string(REGEX REPLACE "/STACK:[0-9]+" "" CMAKE_EXE_LINKER_FLAGS ${CMAKE_EXE_LINKER_FLAGS})
      set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} /STACK:256000000")
  else()
      # mingw
      set(STP_DEFS_COMM ${STP_DEFS_COMM} -DEXT_HASH_MAP)
  endif()
  add_definitions(${STP_DEFS_COMM})
endif()

# -----------------------------------------------------------------------------
# Write out the config.h
# -----------------------------------------------------------------------------

configure_file(
  "${CMAKE_CURRENT_SOURCE_DIR}/src/config.h.in"
  "${CMAKE_CURRENT_BINARY_DIR}/include/config.h"
)
include_directories("${CMAKE_CURRENT_BINARY_DIR}/include")

# -----------------------------------------------------------------------------
# Uncomment these for static compilation under Linux (messes up Valgrind)
# -----------------------------------------------------------------------------

#set (STATICCOMPILE 1)
if(STATICCOMPILE AND (${CMAKE_SYSTEM_NAME} MATCHES "Linux"))
    set(CMAKE_EXE_LINKER_FLAGS "-static")
    set(CMAKE_FIND_LIBRARY_SUFFIXES ".a")
endif()

# -----------------------------------------------------------------------------
# Add Git revision
# -----------------------------------------------------------------------------

include(GetGitRevisionDescription)
get_git_head_revision(GIT_REFSPEC GIT_SHA1)

# -----------------------------------------------------------------------------
# Find the Boost package components
# -----------------------------------------------------------------------------

#SET(Boost_USE_STATIC_LIBS ON)
find_package( Boost 1.46 REQUIRED COMPONENTS program_options system)

# -----------------------------------------------------------------------------
# Compile all subdirs
# -----------------------------------------------------------------------------

add_subdirectory(src)

# -----------------------------------------------------------------------------
# Copy built binaries to root (build) dir
# -----------------------------------------------------------------------------

add_custom_target(copy ALL COMMENT "Copying binaries from subdirs to build directory")
add_custom_command(
  TARGET copy
  COMMAND ${CMAKE_COMMAND} -E copy src/main/stp .
)
add_dependencies(copy
  stp
)

enable_testing()

add_test(NAME regresscvc
  WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/scripts/
  COMMAND scripts/run_tests.pl --td=${CMAKE_CURRENT_SOURCE_DIR}/big-test/
)
#regresscvc: REGRESS_LOG=`date +%Y-%m-%d`"-regress-cvc.log"
#regresscvc: baseTest
