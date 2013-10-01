project(STP)
cmake_minimum_required(VERSION 2.8.8 FATAL_ERROR)

# Search paths for custom CMake modules
set(CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/cmake/modules)

# -----------------------------------------------------------------------------
# Make RelWithDebInfo the default build type if otherwise not set
# -----------------------------------------------------------------------------

if(NOT CMAKE_BUILD_TYPE)
      set(build_types Debug Release RelWithDebInfo MinSizeRel)

      message(STATUS "You can choose the type of build, options are:${build_types}")
      set(CMAKE_BUILD_TYPE RelWithDebInfo CACHE String
          "Options are ${build_types}"
          FORCE
         )

      # Provide drop down menu options in cmake-gui
      set_property(CACHE CMAKE_BUILD_TYPE PROPERTY STRINGS ${build_types})
endif()
message(STATUS "Doing a ${CMAKE_BUILD_TYPE} build")

# -----------------------------------------------------------------------------
# Enable LLVM sanitizations.
# Note that check_cxx_compiler_flag doesn't work, a fix is needed here
# -----------------------------------------------------------------------------
macro(add_cxx_flag flagname)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${flagname}")
endmacro()

#set(SANITIZE 1)
if (SANITIZE)
    SET (CMAKE_CXX_COMPILER "clang++")
    add_cxx_flag("-fsanitize=return")
    add_cxx_flag("-fsanitize=bounds")
    add_cxx_flag("-fsanitize=integer")
    add_cxx_flag("-fsanitize=undefined")
    add_cxx_flag("-fsanitize=float-divide-by-zero")
    add_cxx_flag("-fsanitize=integer-divide-by-zero")
    add_cxx_flag("-fsanitize=null")
    add_cxx_flag("-fsanitize=unsigned-integer-overflow")
    add_cxx_flag("-fsanitize=address")
    add_cxx_flag("-Wno-bitfield-constant-conversion")
endif()

# -----------------------------------------------------------------------------
# Let the user decide if they want to build shared or static client library.
# STP will link against this client library
# -----------------------------------------------------------------------------
option(BUILD_SHARED_LIBS "Build client library as a shared library" OFF)

# -----------------------------------------------------------------------------
# Set the appropriate build flags
# -----------------------------------------------------------------------------
include(CheckCXXCompilerFlag)

macro(add_cxx_flag_if_supported flagname)
  check_cxx_compiler_flag("${flagname}" HAVE_FLAG_${flagname})

  if(HAVE_FLAG_${flagname})
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${flagname}")
  endif()
endmacro()

if(BUILD_SHARED_LIBS)
    message(STATUS "Building shared library currently broken due to mix of C++/C code")
    add_cxx_flag_if_supported("-fPIC")
endif()

check_cxx_compiler_flag("-std=gnu++11" HAVE_FLAG_STD_GNUPP11)
check_cxx_compiler_flag("-std=c++11" HAVE_FLAG_STD_CPP11)
check_cxx_compiler_flag("-std=c++0x" HAVE_FLAG_STD_CPP0X)
check_cxx_compiler_flag("-stdlib=libc++" HAVE_FLAG_STDLIB_LIBCPP)

if(HAVE_FLAG_STD_GNUCPP11)
  set(CMAKE_CXX_FLAGS "-std=gnu++11 ${CMAKE_CXX_FLAGS}")
elseif(HAVE_FLAG_STD_CPP11)
  set(CMAKE_CXX_FLAGS "-std=c++11 ${CMAKE_CXX_FLAGS}")
elseif(HAVE_FLAG_STD_CPP0X)
  set(CMAKE_CXX_FLAGS "-std=c++0x ${CMAKE_CXX_FLAGS}")
endif()

if(APPLE AND HAVE_FLAG_STDLIB_LIBCPP)
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -stdlib=libc++")
endif()

add_cxx_flag_if_supported("-Wall")
add_cxx_flag_if_supported("-Wextra")
add_cxx_flag_if_supported("-Wunused")
add_cxx_flag_if_supported("-Wsign-compare")
add_cxx_flag_if_supported("-Wtype-limits")
add_cxx_flag_if_supported("-Wuninitialized")
add_cxx_flag_if_supported("-Wno-deprecated")
add_cxx_flag_if_supported("-Wstrict-aliasing")
add_cxx_flag_if_supported("-Wpointer-arith")
add_definitions("-D__STDC_LIMIT_MACROS")

option(TUNE_NATIVE "Use -mtune=native" OFF)
if(TUNE_NATIVE)
  add_cxx_flag_if_supported("-mtune=native")
endif()



if(WIN32)
  # build shared lib on windows is not prepared at source level
  set(BUILD_SHARED_LIBS OFF)
  message(WARNING "Disabling building of shared library on Windows")
  set(FLEX_PATH_HINT "e:/cygwin/bin" CACHE STRING "Flex path hints, can be null if on your path")
  set(BISON_PATH_HINT "e:/cygwin/bin" CACHE STRING "Bison path hints, can be null if on your path")
  set(PERL_PATH_HINT "C:/Perl/bin" CACHE STRING "Perl path hints, can be null if on your pat")

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
# Determine the locations of C++ hash_set and hash_map
# -----------------------------------------------------------------------------

include(CheckCxxHashSet)
check_cxx_hashset()

include(CheckCxxHashMultiSet)
check_cxx_hashmultiset()

include(CheckCxxHashMap)
check_cxx_hashmap()

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

# -----------------------------------------------------------------------------
# Add Git revision
# -----------------------------------------------------------------------------

include(GetGitRevisionDescription)
get_git_head_revision(GIT_REFSPEC GIT_SHA1)

# -----------------------------------------------------------------------------
# Find the Boost package components
# -----------------------------------------------------------------------------

if(NOT BUILD_SHARED_LIBS)
    # If we are building libstp as static we will want to 
    # make sure there are no unresolved symbols to Boost
    # library functions. Later we'll merge them into the
    # archive so we'll need static boost libraries.
    message("Trying to use static Boost libraries")
    set(Boost_USE_STATIC_LIBS ON)
endif()
find_package( Boost 1.46 REQUIRED COMPONENTS program_options system)
include_directories(${Boost_INCLUDE_DIRS})

find_package(BISON REQUIRED)
find_package(FLEX REQUIRED)

# -----------------------------------------------------------------------------
# Setup library output path
# -----------------------------------------------------------------------------
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)

# -----------------------------------------------------------------------------
# This macro creates a custom target that copies various header files into
# in ${CMAKE_CURRENT_SOURCE_DIR} into ${CMAKE_BINARY_DIR}/include/stp
# It also specifies that these header files should be installed.
#
# Usage: copy_public_headers(NAME HEADER_LIST)
# NAME : The name for the set headers it should not contains spaces
# HEADER_LIST : A list of header files. You should quote this 
#               e.g. "${my_headers}"
# -----------------------------------------------------------------------------
macro(copy_public_headers NAME HEADER_LIST)
add_custom_target(CopyPublic_${NAME}_Headers ALL)
    foreach(public_header ${HEADER_LIST})
        add_custom_command(TARGET CopyPublic_${NAME}_Headers PRE_BUILD
                           COMMAND ${CMAKE_COMMAND} -E
                               echo Copying public ${NAME}header ${public_header}
                           COMMAND ${CMAKE_COMMAND} -E
                               copy ${CMAKE_CURRENT_SOURCE_DIR}/${public_header}
                                    ${CMAKE_BINARY_DIR}/include/stp/${public_header}
                          )
        install(FILES ${public_header} DESTINATION include/)
    endforeach()
endmacro()

# -----------------------------------------------------------------------------
# Compile all subdirs
# -----------------------------------------------------------------------------

add_subdirectory(src)

# -----------------------------------------------------------------------------
# Add uninstall target for makefiles
# -----------------------------------------------------------------------------
configure_file(
    "${CMAKE_CURRENT_SOURCE_DIR}/cmake/modules/cmake_uninstall.cmake.in"
    "${CMAKE_CURRENT_BINARY_DIR}/cmake_uninstall.cmake"
    IMMEDIATE @ONLY)

add_custom_target(uninstall
    COMMAND ${CMAKE_COMMAND} -P ${CMAKE_CURRENT_BINARY_DIR}/cmake_uninstall.cmake)

# -----------------------------------------------------------------------------
# Testing
# -----------------------------------------------------------------------------

enable_testing()

add_test(NAME regresscvc
  WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/scripts/
  COMMAND run_tests.pl --td=${CMAKE_CURRENT_SOURCE_DIR}/big-test/
)
#regresscvc: REGRESS_LOG=`date +%Y-%m-%d`"-regress-cvc.log"
#regresscvc: baseTest
