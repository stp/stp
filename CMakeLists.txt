cmake_minimum_required(VERSION 2.6 FATAL_ERROR)

# -----------------------------------------------------------------------------
# Make RelWithDebInfo the default build type if otherwise not set
# -----------------------------------------------------------------------------
IF(DEFINED CMAKE_BUILD_TYPE)
  SET(CMAKE_BUILD_TYPE ${CMAKE_BUILD_TYPE}
  CACHE STRING "Choose the type of build: None(CMAKE_CXX_FLAGS or CMAKE_C_FLAGS used) Debug Release RelWithDebInfo MinSizeRel.")
ELSE()
  SET(CMAKE_BUILD_TYPE RelWithDebInfo CACHE STRING
  "Choose the type of build, options are: None(CMAKE_CXX_FLAGS or CMAKE_C_FLAGS used) Debug Release RelWithDebInfo MinSizeRel.")
ENDIF()

PROJECT(stp)
#m4-extra contains some library search cmake stuff
SET(CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/m4-extra)

#set(LLVM 1)
if (LLVM)
    SET (CMAKE_C_COMPILER             "/usr/bin/clang")
    SET (CMAKE_C_FLAGS                "-Wall -std=c99")
    SET (CMAKE_C_FLAGS_DEBUG          "-g")
    SET (CMAKE_C_FLAGS_MINSIZEREL     "-Os -DNDEBUG")
    SET (CMAKE_C_FLAGS_RELEASE        "-O4 -DNDEBUG")
    SET (CMAKE_C_FLAGS_RELWITHDEBINFO "-O2 -g")

    SET (CMAKE_CXX_COMPILER             "/usr/bin/clang++")
    SET (CMAKE_CXX_FLAGS                "-Wall")
    SET (CMAKE_CXX_FLAGS_DEBUG          "-g")
    SET (CMAKE_CXX_FLAGS_MINSIZEREL     "-Os -DNDEBUG")
    SET (CMAKE_CXX_FLAGS_RELEASE        "-O4 -DNDEBUG")
    SET (CMAKE_CXX_FLAGS_RELWITHDEBINFO "-O2 -g")

    SET (CMAKE_AR      "/usr/bin/llvm-ar")
    SET (CMAKE_LINKER  "/usr/bin/llvm-ld")
    SET (CMAKE_NM      "/usr/bin/llvm-nm")
    SET (CMAKE_OBJDUMP "/usr/bin/llvm-objdump")
    SET (CMAKE_RANLIB  "/usr/bin/llvm-ranlib")

else (LLVM)
    SET(CMAKE_CXX_FLAGS_RELWITHDEBINFO "-Wno-deprecated -D __STDC_LIMIT_MACROS -D __STDC_FORMAT_MACROS -DEXT_HASH_MAP -O1 -mtune=native")
#        "-std=c++0x -pedantic -Wall -Wextra -Wunused -Wsign-compare -Wtype-limits -Wuninitialized -Wno-deprecated -g -fno-omit-frame-pointer -O4 -mtune=native")
    SET(CMAKE_CXX_FLAGS_DEBUG "-std=c++0x -Wunused -Wsign-compare -Wtype-limits -Wuninitialized -Wall -Wno-deprecated -O0 -ggdb")
    SET(CMAKE_CXX_FLAGS_RELEASE "-std=c++0x -O2 -g -DNDEBUG -mtune=native")
endif(LLVM)

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
else(MSVC)
    # mingw
    set(STP_DEFS_COMM ${STP_DEFS_COMM} -DEXT_HASH_MAP)
endif(MSVC)
add_definitions(${STP_DEFS_COMM})
endif(WIN32)



# -----------------------------------------------------------------------------
# Uncomment these for static compilation under Linux (messes up Valgrind)
# -----------------------------------------------------------------------------
#set (STATICCOMPILE 1)
IF(STATICCOMPILE AND (${CMAKE_SYSTEM_NAME} MATCHES "Linux"))
    SET(CMAKE_EXE_LINKER_FLAGS "-static")
    set(CMAKE_FIND_LIBRARY_SUFFIXES ".a")
ENDIF(STATICCOMPILE AND (${CMAKE_SYSTEM_NAME} MATCHES "Linux"))

# -----------------------------------------------------------------------------
# Add GIT version
# -----------------------------------------------------------------------------
include(GetGitRevisionDescription)
get_git_head_revision(GIT_REFSPEC GIT_SHA1)

# Look for Boost program options
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











