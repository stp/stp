# AUTHORS: Dan Liew, Ryan Govostes, Mate Soos
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
# THE SOFTWARE.

# 3.18 is what lib/extlib-mimalloc requires, and mimalloc is the default
# STP_ALLOCATOR, so a default build already needs it. Anyone on an older CMake
# can configure with -DSTP_ALLOCATOR=system, which skips that subdirectory.
#
# Nothing here sets a policy explicitly: every policy STP cares about
# (CMP0048, CMP0074, CMP0077, CMP0092 - the newest introduced in 3.15) is NEW
# by default at this minimum.
cmake_minimum_required(VERSION 3.18)

project(STP)

set(CMAKE_C_STANDARD 99)
set(CMAKE_CXX_STANDARD 17)

include(GNUInstallDirs)
include(FeatureSummary)

# Search paths for custom CMake modules. cmake/ holds the per-dependency Find
# modules; cmake/modules/ holds everything else STP carries.
set(CMAKE_MODULE_PATH
    ${PROJECT_SOURCE_DIR}/cmake
    ${PROJECT_SOURCE_DIR}/cmake/modules
)

include(STPOptions)
include(FetchContent)

# Where the scripts/deps/*.sh scripts install. Appended, so that a dependency
# this build produced in STP_DEP_DIR -- which deps-helper prepends -- outranks
# one left behind by an earlier hand-run script.
list(APPEND CMAKE_PREFIX_PATH "${PROJECT_SOURCE_DIR}/deps/install")

# generate JSON file of compile commands -- useful for code extension
set(CMAKE_EXPORT_COMPILE_COMMANDS 1)

set(INCLUDEDIR include CACHE STRING "Output directory for include headers")
set(STP_TIMESTAMPS ON CACHE BOOL "Enable build with timestamps")

# -----------------------------------------------------------------------------
# Make RelWithDebInfo the default build type if otherwise not set
# -----------------------------------------------------------------------------
set(build_types Debug Release RelWithDebInfo MinSizeRel)
if(NOT CMAKE_BUILD_TYPE)

      message(STATUS "You can choose the type of build, options are: ${build_types}")
      set(CMAKE_BUILD_TYPE RelWithDebInfo CACHE STRING
          "Options are ${build_types}"
          FORCE
         )

      # Provide drop down menu options in cmake-gui
      set_property(CACHE CMAKE_BUILD_TYPE PROPERTY STRINGS ${build_types})
endif()
message(STATUS "Doing a ${CMAKE_BUILD_TYPE} build")

# -----------------------------------------------------------------------------
# Option to enable/disable assertions
# -----------------------------------------------------------------------------

# Filter out definition of NDEBUG from the default build configuration flags.
# We will add this ourselves if we want to disable assertions
foreach (build_config ${build_types})
    string(TOUPPER ${build_config} upper_case_build_config)
    foreach (language CXX C)
        set(VAR_TO_MODIFY "CMAKE_${language}_FLAGS_${upper_case_build_config}")
        string(REGEX REPLACE "(^| )[/-]D *NDEBUG($| )"
                             " "
                             replacement
                             "${${VAR_TO_MODIFY}}"
              )
        #message("Original (${VAR_TO_MODIFY}) is ${${VAR_TO_MODIFY}} replacement is ${replacement}")
        set(${VAR_TO_MODIFY} "${replacement}" CACHE STRING "Default flags for ${build_config} configuration" FORCE)
    endforeach()
endforeach()

# Three-valued, so that the build type can supply a default without silently
# overruling a choice. It used to be a plain option() defaulting ON with an
# unconditional set(ENABLE_ASSERTIONS OFF) for Release underneath it, which
# meant -DENABLE_ASSERTIONS=ON -DCMAKE_BUILD_TYPE=Release quietly produced a
# build with no assertions in it -- the request was accepted and discarded.
stp_migrate_bool_option(ENABLE_ASSERTIONS)
stp_option(ENABLE_ASSERTIONS "Build with assertions enabled")
if(CMAKE_BUILD_TYPE STREQUAL "Release")
    # Release means "ship this", so no assertions unless they were asked for.
    stp_set_option(ENABLE_ASSERTIONS OFF)
endif()
stp_set_option(ENABLE_ASSERTIONS ON)

if (ENABLE_ASSERTIONS)
    # NDEBUG was already removed.
else()
    # Note this definition doesn't appear in the cache variables.
    add_definitions(-DNDEBUG)
endif()
add_feature_info(Assertions ENABLE_ASSERTIONS "Enables assertions")

# -----------------------------------------------------------------------------
# Enable LLVM sanitizations.
# Note that check_cxx_compiler_flag doesn't work, a fix is needed here
# -----------------------------------------------------------------------------
macro(add_cxx_flag flagname)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${flagname}")
endmacro()

option(SANITIZE "Use Clang sanitizers" OFF)
if (SANITIZE)
    # Set in Cache so user can tweak it later
    SET(CMAKE_CXX_COMPILER "clang++" CACHE FILEPATH "" FORCE)
    message(STATUS "Forcing compiler: ${CMAKE_CXX_COMPILER}")
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
add_feature_info(Sanitizers SANITIZE "Enables Clang sanitizers, will force using clang++ as the compiler")

# -----------------------------------------------------------------------------
# Let the user decide if they want to build shared or static client library.
# STP will link against this client library
# -----------------------------------------------------------------------------

option(BUILD_SHARED_LIBS "Build the shared library" ON)
option(STATICCOMPILE "Compile static library and executable" OFF)
if (STATICCOMPILE)
    set(BUILD_SHARED_LIBS OFF)
    set(ENABLE_PYTHON_INTERFACE OFF)
endif()
add_feature_info(Static STATICCOMPILE "Compiles static library and executable")

if ((${CMAKE_SYSTEM_NAME} MATCHES "Windows") OR (NOT BUILD_SHARED_LIBS))
    set(Minisat_USE_STATIC_LIBS ON)
endif()

if (NOT BUILD_SHARED_LIBS)
    if (NOT MSVC)
        set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -static -Wl,--whole-archive -lpthread -Wl,--no-whole-archive -static ")
        set(CMAKE_FIND_LIBRARY_SUFFIXES ".a")

        # removing -rdynamic that's automatically added
        foreach (language CXX C)
            set(VAR_TO_MODIFY "CMAKE_SHARED_LIBRARY_LINK_${language}_FLAGS")
            string(REGEX REPLACE "(^| )-rdynamic($| )"
                                 " "
                                 replacement
                                 "${${VAR_TO_MODIFY}}")
            #message("Original (${VAR_TO_MODIFY}) is ${${VAR_TO_MODIFY}} replacement is ${replacement}")
            set(${VAR_TO_MODIFY} "${replacement}" CACHE STRING "Default flags for ${build_config} configuration" FORCE)
        endforeach()
    endif()
else ()
    # use, i.e. don't skip the full RPATH for the build tree
    SET(CMAKE_SKIP_BUILD_RPATH  FALSE)

    # when building, don't use the install RPATH already
    # (but later on when installing)
    SET(CMAKE_BUILD_WITH_INSTALL_RPATH FALSE)

    SET(CMAKE_INSTALL_RPATH "${CMAKE_INSTALL_FULL_LIBDIR}")

    # add the automatically determined parts of the RPATH
    # which point to directories outside the build tree to the install RPATH
    SET(CMAKE_INSTALL_RPATH_USE_LINK_PATH TRUE)

    # the RPATH to be used when installing, but only if it's not a system directory
    LIST(FIND CMAKE_PLATFORM_IMPLICIT_LINK_DIRECTORIES "${CMAKE_INSTALL_FULL_LIBDIR}" isSystemDir)
    IF("${isSystemDir}" STREQUAL "-1")
        SET(CMAKE_INSTALL_RPATH "${CMAKE_INSTALL_FULL_LIBDIR}")
    ENDIF("${isSystemDir}" STREQUAL "-1")

    if (APPLE)
      set(CMAKE_MACOSX_RPATH ON)
      set(CMAKE_INSTALL_RPATH "@loader_path/../lib")
      message(STATUS "Using RPATH for dynamic linking")
    endif()
endif()

option(SUPPRESS_WARNINGS "Silence all warnings" OFF)

if (NOT MSVC)
    add_compile_options( -g)
    add_compile_options( -pthread )

    add_compile_options("$<$<CONFIG:RELWITHDEBINFO>:-O2>")

    add_compile_options("$<$<CONFIG:RELEASE>:-O3>")
    add_compile_options("$<$<CONFIG:RELEASE>:-fno-tree-vectorize>")
    add_compile_options("$<$<CONFIG:RELEASE>:-g0>")

    add_compile_options("$<$<CONFIG:DEBUG>:-O0>")

    if(NOT CMAKE_BUILD_TYPE STREQUAL "Debug")
        set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} -O2")
        set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -O2")
    endif()
else()
    # see https://msdn.microsoft.com/en-us/library/fwkeyyhe.aspx for details
    # /Z7 = include debug info
    # /Wall = all warnings

    add_compile_options("$<$<CONFIG:RELWITHDEBINFO>:/O2>")
    # /Z7 rather than /ZI or /Zi. Both of those write every object's debug
    # information into one shared PDB through mspdbsrv, which a parallel build
    # has to serialise on (/FS exists only to make that safe at all), and which
    # a compiler cache cannot reproduce when it replays a hit -- sccache
    # declines to cache anything compiled that way. /Z7 puts the same debug
    # information in the object file itself, so it is per-object, needs no
    # serialisation and survives caching; the linker still emits a PDB from it.
    # /ZI additionally asks for Edit and Continue, which is a debugger feature
    # of no use to a build, and which cl does not honour alongside the /O2
    # above in any case.
    add_compile_options("$<$<CONFIG:RELWITHDEBINFO>:/Z7>")

    add_compile_options("$<$<CONFIG:RELEASE>:/O2>")
    add_compile_options("$<$<CONFIG:RELEASE>:/D>")
    add_compile_options("$<$<CONFIG:RELEASE>:/NDEBUG>")

    add_compile_options("$<$<CONFIG:DEBUG>:/Od>")

    if (NOT BUILD_SHARED_LIBS)
        # We statically link to reduce dependencies
        foreach(flag_var CMAKE_CXX_FLAGS CMAKE_CXX_FLAGS_DEBUG CMAKE_CXX_FLAGS_RELEASE CMAKE_CXX_FLAGS_MINSIZEREL CMAKE_CXX_FLAGS_RELWITHDEBINFO)
            # /MD -- Causes the application to use the multithread-specific
            #        and DLL-specific version of the run-time library.
            #        Defines _MT and _DLL and causes the compiler to place
            #        the library name MSVCRT.lib into the .obj file.
            if(${flag_var} MATCHES "/MD")
                string(REGEX REPLACE "/MD" "/MT" ${flag_var} "${${flag_var}}")
            endif(${flag_var} MATCHES "/MD")

            # /MDd	-- Defines _DEBUG, _MT, and _DLL and causes the application to use the debug multithread-specific and DLL-specific version of the run-time library.
            #          It also causes the compiler to place the library name MSVCRTD.lib into the .obj file.
            if(${flag_var} MATCHES "/MDd")
                string(REGEX REPLACE "/MDd" "/MTd" ${flag_var} "${${flag_var}}")
            endif(${flag_var} MATCHES "/MDd")
        endforeach(flag_var)

        # Creates a multithreaded executable (static) file using LIBCMT.lib.
        add_compile_options(/MT)
    endif()

    # buffers security check
    add_compile_options(/GS)

    # Proper warning level
    if(SUPPRESS_WARNINGS)
        add_compile_options(/W0)
    else()
        add_compile_options(/W1)
    endif()

    # Disable STL used in DLL-boundary warning
    add_compile_options(/wd4251)
    add_compile_options(/D_CRT_SECURE_NO_WARNINGS)

    # Wall is MSVC's Weverything, so annoying unless used from the start
    # and with judiciously used warning disables
    # add_compile_options(/Wall)

    # /Za = only ansi C98 & C++11
    # /Za is not recommended for use, not tested, etc.
    # see: http://stackoverflow.com/questions/5489326/za-compiler-directive-does-not-compile-system-headers-in-vs2010
    # add_compile_options(/Za)

    add_compile_options(/fp:precise)

    # exception handling. s = The exception-handling model that catches C++ exceptions only and tells the compiler to assume that functions declared as extern "C" may throw an exception.
    # exception handling. c = If used with s (/EHsc), catches C++ exceptions only and tells the compiler to assume that functions declared as extern "C" never throw a C++ exception.
    add_compile_options(/EHsc)


    # set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} /INCREMENTAL:NO")
    # set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} /PDBCOMPRESS")
    set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} /STACK:1572864")

    if (MSVC)
        # Windows compatibility includes
        set(STP_DEFS_COMM ${STP_DEFS_COMM} -D_CRT_SECURE_NO_WARNINGS)
        set(STP_INCL_COMM windows/winports ${STP_INCL_COMM})
        include_directories(${STP_INCL_COMM})
        add_subdirectory(windows)
        set(PLATFORM_COMPAT_LIBRARIES ${PLATFORM_COMPAT_LIBRARIES} windows_compat)
        set(CMAKE_FIND_LIBRARY_SUFFIXES .lib .a ${CMAKE_FIND_LIBRARY_SUFFIXES})

        # stack size of MSVC must be specified
        string(REGEX REPLACE "/STACK:[0-9]+" "" CMAKE_EXE_LINKER_FLAGS ${CMAKE_EXE_LINKER_FLAGS})
        set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} /STACK:512000000")

        # inline is not a keyword in visual studios old C version, allow its redefinition
        add_definitions("-D_ALLOW_KEYWORD_MACROS")
    endif()

endif()

# -----------------------------------------------------------------------------
# Set the appropriate build flags
# -----------------------------------------------------------------------------
include(CheckCXXCompilerFlag)
include(CheckLinkerFlag)

macro(add_cxx_flag_if_supported flagname)
  check_cxx_compiler_flag("${flagname}" HAVE_FLAG_${flagname})

  if(HAVE_FLAG_${flagname})
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${flagname}")
  endif()
endmacro()

check_cxx_compiler_flag("-std=c++11" HAVE_FLAG_STD_CPP11)

if(APPLE)
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -stdlib=libc++")
endif()

if(NOT MSVC)
    if(SUPPRESS_WARNINGS)
        add_cxx_flag_if_supported("-w")
    else()
        add_cxx_flag_if_supported("-Wall")
        add_cxx_flag_if_supported("-Wextra")
        add_cxx_flag_if_supported("-Wunused")
        add_cxx_flag_if_supported("-pedantic")
        add_cxx_flag_if_supported("-Wsign-compare")
        add_cxx_flag_if_supported("-Wtype-limits")
        add_cxx_flag_if_supported("-Wuninitialized")
        add_cxx_flag_if_supported("-Wno-deprecated")
        add_cxx_flag_if_supported("-Wstrict-aliasing")
        add_cxx_flag_if_supported("-Wpointer-arith")
        add_cxx_flag_if_supported("-Wheader-guard")
        add_cxx_flag_if_supported("-Wpointer-arith")
        add_cxx_flag_if_supported("-Wformat-nonliteral")
        add_cxx_flag_if_supported("-Winit-self")
        add_cxx_flag_if_supported("-Wparentheses")
        add_cxx_flag_if_supported("-Wunreachable-code")
    endif()

    if (NOT CMAKE_BUILD_TYPE STREQUAL "Release")
        add_cxx_flag_if_supported("-fno-omit-frame-pointer")
    endif()
    if(${CMAKE_SYSTEM_NAME} MATCHES "Linux")
        # Cut the cost of dynamic symbol resolution, which is ~79% of STP's
        # fixed 4.15M-instruction startup and so dominates easy queries.
        #
        # -fvisibility=hidden exports only what is explicitly annotated
        # DLL_PUBLIC (see include/stp/Util/Attributes.h), which is the whole
        # public C and C++ API.  Everything else becomes local, so the loader
        # has far fewer symbols to look up.
        #
        # -Wl,-Bsymbolic-functions binds libstp's calls to its own exported
        # functions at link time instead of going through the PLT.  The one
        # consequence is that LD_PRELOAD can no longer interpose STP's own
        # functions on calls made from inside libstp; that is not a use case
        # for a solver library, and the flag is in Debian's default hardening
        # set.  Neither flag changes behaviour: the emitted CNF is unchanged.
        #
        # -fvisibility=hidden is skipped for ENABLE_TESTING and
        # BUILD_EXTRA_TOOLS builds.  The unit tests and the extra tools
        # (propagator_bench and friends) link libstp and call directly into
        # entry points that are not part of the public API (the simplifier
        # passes, the domain analyses, STPMgr internals, SMT2ScanString), so
        # they need the full export set.  This is why the flag was carried
        # commented-out here.
        if(NOT ENABLE_TESTING AND NOT BUILD_EXTRA_TOOLS)
            add_cxx_flag_if_supported("-fvisibility=hidden")
            # The vendored ABC sources are C.  There is no
            # add_c_flag_if_supported, so reuse the check above and set
            # CMAKE_C_FLAGS directly, as WERROR does.
            if(HAVE_FLAG_-fvisibility=hidden)
                set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -fvisibility=hidden")
            endif()
        endif()

        check_linker_flag(CXX "-Wl,-Bsymbolic-functions" HAVE_LINKER_FLAG_BSYMBOLIC_FUNCTIONS)
        if(HAVE_LINKER_FLAG_BSYMBOLIC_FUNCTIONS)
            set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} -Wl,-Bsymbolic-functions")
            set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -Wl,-Bsymbolic-functions")
        endif()

        set(CMAKE_EXE_LINKER_FLAGS " ${CMAKE_EXE_LINKER_FLAGS} -Wl,--discard-all -Wl,--build-id=sha1")
    endif()
    # add_cxx_flag_if_supported("-flto") # slow compile and not enough benefits
    set(CMAKE_POSITION_INDEPENDENT_CODE ON)
endif()

add_definitions("-D__STDC_LIMIT_MACROS")

option(TUNE_NATIVE "Use -mtune=native" OFF)
if(TUNE_NATIVE)
  add_cxx_flag_if_supported("-mtune=native")
endif()

# Let the compiler emit the POPCNT instruction.  Without this, popCount64() in
# include/stp/Util/BitOps.h counts in software, because gcc's default x86-64
# target has no POPCNT and __builtin_popcountll would otherwise become an
# out-of-line call into libgcc.  Note TUNE_NATIVE does not imply this: -mtune
# only changes scheduling, not the instructions the compiler may emit.
#
# On by default -- POPCNT is on every x86-64 CPU since Nehalem (2008) and AMD
# Barcelona (2007).  Turn it off when building for hardware older than that,
# such as a distribution package targeting the baseline x86-64 ISA; the
# software fallback in BitOps.h is then used and remains correct everywhere.
option(USE_POPCNT "Use the POPCNT instruction (requires Nehalem/2008 or later)" ON)
if(USE_POPCNT)
  add_cxx_flag_if_supported("-mpopcnt")
  # The vendored ABC sources are C.  There is no add_c_flag_if_supported, so
  # reuse the check above and set CMAKE_C_FLAGS directly, as WERROR does.
  if(HAVE_FLAG_-mpopcnt)
    set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -mpopcnt")
  endif()
endif()

option(COVERAGE "Build with coverage check" OFF)
if (COVERAGE)
    add_cxx_flag("--coverage")
endif()

option(WERROR "Build with warnings as errors" OFF)
if (WERROR)
    if (NOT MSVC)
        message(STATUS "Enabling treating warnings as errors")
        # Let's make things be errors -- we can't test for this
        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Werror")
        set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -Werror")
    else()
        message(STATUS "Warnings as errors is not enabled under MSVC")
    endif()
endif()

option(USE_THREAD_LOCAL "Use thread-local storage when available" ON)
add_feature_info(ThreadLocal USE_THREAD_LOCAL "Enables use of thread-local storage when available")

if(WIN32)
  set(FLEX_PATH_HINT "e:/cygwin/bin" CACHE STRING "Flex path hints, can be null if on your path")
  set(BISON_PATH_HINT "e:/cygwin/bin" CACHE STRING "Bison path hints, can be null if on your path")
  set(PHINTS ${FLEX_PATH_HINT} ${BISON_PATH_HINT})
  add_definitions(${STP_DEFS_COMM})
endif()

# -----------------------------------------------------------------------------
# Add GIT version
# -----------------------------------------------------------------------------
function(SetVersionNumber PREFIX VERSION_MAJOR VERSION_MINOR VERSION_PATCH)
  set(${PREFIX}_VERSION_MAJOR ${VERSION_MAJOR} PARENT_SCOPE)
  set(${PREFIX}_VERSION_MINOR ${VERSION_MINOR} PARENT_SCOPE)
  set(${PREFIX}_VERSION_PATCH ${VERSION_PATCH} PARENT_SCOPE)
  set(${PREFIX}_VERSION
        "${VERSION_MAJOR}.${VERSION_MINOR}.${VERSION_PATCH}"
        PARENT_SCOPE)
endfunction()

find_program (GIT_EXECUTABLE git)
if (GIT_EXECUTABLE)
  include(GetGitRevisionDescription)
  get_git_head_revision(GIT_REFSPEC GIT_SHA)
  MESSAGE(STATUS "GIT hash found: ${GIT_SHA}")
else()
  set(GIT_SHA "GIT-hash-notfound")
endif()
set(STP_FULL_VERSION "2.4.1")

string(REPLACE "." ";" STP_FULL_VERSION_LIST ${STP_FULL_VERSION})
SetVersionNumber("PROJECT" ${STP_FULL_VERSION_LIST})
MESSAGE(STATUS "PROJECT_VERSION: ${PROJECT_VERSION}")
MESSAGE(STATUS "PROJECT_VERSION_MAJOR: ${PROJECT_VERSION_MAJOR}")
MESSAGE(STATUS "PROJECT_VERSION_MINOR: ${PROJECT_VERSION_MINOR}")
MESSAGE(STATUS "PROJECT_VERSION_PATCH: ${PROJECT_VERSION_PATCH}")

# -----------------------------------------------------------------------------
# Write out the config.h
# -----------------------------------------------------------------------------

configure_file(
  "${CMAKE_CURRENT_SOURCE_DIR}/include/stp/config.h.in"
  "${CMAKE_CURRENT_BINARY_DIR}/include/stp/config.h"
)

# -----------------------------------------------------------------------------
# Set up includes
# -----------------------------------------------------------------------------
include_directories("${CMAKE_CURRENT_SOURCE_DIR}/include")
include_directories("${CMAKE_CURRENT_BINARY_DIR}/include")

# FIXME: External library includes
include_directories(# For extlib-constbv
                    ${PROJECT_SOURCE_DIR}/lib
                   )

# -----------------------------------------------------------------------------
# ankerl::unordered_dense
# -----------------------------------------------------------------------------
# A single header, used in place of std::unordered_map where it pays off. It
# used to be a copy of that header sitting in lib/extlib-unordered-dense; there
# is no reason for STP to carry upstream's file, so it is fetched at a pinned
# release like everything else.
#
# FetchContent rather than an ExternalProject, and for once not because
# anything has to be compiled: stp/AST/AST.h includes it, so effectively every
# translation unit in STP does, and it is reached through a project-wide
# include rather than through any one target. That leaves nothing for an
# ExternalProject's dependency edge to attach to -- the header would be
# installed at build time, with no ordering guarantee that it lands before the
# first compile that needs it. FetchContent populates during configuration,
# which is the guarantee. There is nothing to build, so that costs nothing.
set(UNORDERED_DENSE_VERSION "4.5.0")
set(UNORDERED_DENSE_CHECKSUM "2364ce4bc4c23bd02549bbb3a7572d881684cd46057f3737fd53be53669743aa")

if(NOT DEFINED FETCHCONTENT_SOURCE_DIR_UNORDEREDDENSE AND NOT ENABLE_AUTO_DOWNLOAD)
    message(FATAL_ERROR
        "ankerl::unordered_dense is required. Configure with "
        "-DENABLE_AUTO_DOWNLOAD=ON to have it fetched, or point "
        "-DFETCHCONTENT_SOURCE_DIR_UNORDEREDDENSE at a checkout.")
endif()

FetchContent_Declare(
    unordereddense
    URL https://github.com/martinus/unordered_dense/archive/refs/tags/v${UNORDERED_DENSE_VERSION}.tar.gz
    URL_HASH SHA256=${UNORDERED_DENSE_CHECKSUM}
    SOURCE_SUBDIR stp-does-not-build-this
)
FetchContent_MakeAvailable(unordereddense)
message(STATUS "ankerl::unordered_dense ${UNORDERED_DENSE_VERSION}: ${unordereddense_SOURCE_DIR}")

# SYSTEM, and project-wide because stp/AST/AST.h reaches it: upstream code
# whose warnings STP does not control, compiled into nearly every translation
# unit here.
include_directories(SYSTEM ${unordereddense_SOURCE_DIR}/include)

# -----------------------------------------------------------------------------
# ABC
# -----------------------------------------------------------------------------
# Looked for after the word-size check below, because ABC_ABI_DEFINITIONS has
# to exist before the Find module can forward it.

# abc related word size check
include(CheckTypeSize)
# Check size of void pointer (void*)
CHECK_TYPE_SIZE("void*" SIZEOF_VOID_P)
# LIN/LIN64 select ABC's Linux code paths, and NT64 the 64-bit Windows
# ones. (abc_global.h only detects the platform by itself when
# ABC_USE_STDINT_H is set; without NT64 its fallback ladder sees MSVC's
# WIN32 and picks a 32-bit ABC_PTRUINT_T, whose tagged AIG pointers
# (Aig_Not/Aig_Regular) truncate 64-bit heap pointers -- the first query
# to reach ABC's CNF generation then dies with an access violation.
# 32-bit Windows is already correct via the WIN32 fallback.)
# These are collected rather than added one at a time, because ABC has to be
# compiled with exactly the same set. They decide the width of ABC_PTRUINT_T,
# and STP's own translation units include ABC's headers -- so if the two
# disagree, ABC's tagged AIG pointers (Aig_Not/Aig_Regular) truncate on one
# side of the boundary and not the other, and the first query to reach CNF
# generation dies. That used to be guaranteed by ABC being added with
# add_subdirectory(), which inherited them; ABC is built separately now, so
# they are forwarded to it explicitly and recorded in the dependency
# directory's stamp.
set(ABC_ABI_DEFINITIONS "")
if(NOT WIN32)
    if(SIZEOF_VOID_P EQUAL 8)
        list(APPEND ABC_ABI_DEFINITIONS -DLIN64)
    else()
        list(APPEND ABC_ABI_DEFINITIONS -DLIN)
    endif()
else()
    if(SIZEOF_VOID_P EQUAL 8)
        list(APPEND ABC_ABI_DEFINITIONS -DNT64)
    endif()
    # ABC is linked statically; without this its headers declare the
    # ABC API __declspec(dllimport), producing unresolved __imp_ symbols.
    list(APPEND ABC_ABI_DEFINITIONS -DWIN32_NO_DLL)
endif()
list(APPEND ABC_ABI_DEFINITIONS -DSIZEOF_VOID_P=${SIZEOF_VOID_P})

# Check size of long
CHECK_TYPE_SIZE("long" SIZEOF_LONG)
list(APPEND ABC_ABI_DEFINITIONS -DSIZEOF_LONG=${SIZEOF_LONG})

# Check size of int
CHECK_TYPE_SIZE("int" SIZEOF_INT)
list(APPEND ABC_ABI_DEFINITIONS -DSIZEOF_INT=${SIZEOF_INT})

# STP's own sources need them too, for the reason above.
add_definitions(${ABC_ABI_DEFINITIONS})

# ABC itself, now that the defines it must be compiled with are known.
find_package(ABC REQUIRED)

# Declared here, well before its first use (the manpage rule); the subdirs it
# gates are added at the bottom of this file.
option(BUILD_EXECUTABLES "Build executables" ON)

# -----------------------------------------------------------------------------
# Dependency machinery
# -----------------------------------------------------------------------------
# Included here, and not up with the other includes, because
# STP_EP_COMMON_CMAKE_ARGS captures CMAKE_CXX_FLAGS in order to hand STP's own
# toolchain to anything it builds -- and those flags are not finished being
# assembled until above this line. Included from up there, a sanitizer build
# would compile its dependencies without the sanitizer, and the mismatch would
# surface as a link failure with nothing pointing back here.
include(deps-helper)

# -----------------------------------------------------------------------------
# Find Riss
# -----------------------------------------------------------------------------
option(USE_MINISAT "Use the MiniSat solver backend" OFF)
add_feature_info(MiniSat USE_MINISAT "Enables the MiniSat and simplifying-MiniSat solvers")

option(USE_RISS "Try to use Riss" OFF)
add_feature_info(Riss USE_RISS "Enables Riss solver")

if (USE_RISS)
    # RISS_DIR still names a Riss checkout; cmake/FindRiss.cmake keeps that as
    # its first choice and can build one otherwise.
    find_package(Riss REQUIRED)
    # USE_RISS reaches headers (UserDefinedFlags.h picks the default backend
    # from it), so it has to stay a global definition. The include directory
    # does not: only lib/Sat/RissCore.cpp includes a Riss header, and the Riss
    # target carries it there.
    add_definitions(-DUSE_RISS)
endif()

# -----------------------------------------------------------------------------
# Setup Cadical
# -----------------------------------------------------------------------------
# On by default, and the only backend that is. Something has to be, or a plain
# `cmake ..` has no way to solve anything now that CryptoMiniSat is no longer
# picked up merely for being installed -- and CaDiCaL is the one to pick: it
# needs no system library (CryptoMiniSat wants GMP, MiniSat wants zlib), it is
# the backend the documentation recommends for hard bitvector problems, and
# with -DENABLE_AUTO_DOWNLOAD=ON the build can produce one itself.
option(USE_CADICAL "Use the CaDiCaL solver backend" ON)
add_feature_info(Cadical USE_CADICAL "Enables Cadical solver")

if (USE_CADICAL)
    # CADICAL_DIR still names a checkout, and is still what decides when it is
    # set; cmake/FindCaDiCaL.cmake keeps that, adds an installed CaDiCaL as a
    # second choice, and can build one otherwise. It is also where the version
    # is worked out, and with it whether bounded variable addition
    # (--cadical-factor) can be compiled in.
    find_package(CaDiCaL REQUIRED)
    add_definitions(-DUSE_CADICAL)
    if (CADICAL_HAS_FACTOR)
        add_definitions(-DSTP_CADICAL_HAS_FACTOR)
    endif()
endif()

# -----------------------------------------------------------------------------
# Allocator selection
# -----------------------------------------------------------------------------
# STP is allocation-heavy at every stage: bit-blasting and CNF generation churn
# the AIG and CNF data structures, and the SAT solvers churn clause memory.
# The C library allocator is the bottleneck; any of the modern replacements is
# ~15% faster to CNF, ~14% faster for CaDiCaL solving and ~7% for CryptoMiniSat,
# with identical results. mimalloc is fetched and built as part of STP so that
# a fast allocator is always available, and is what you get unless you ask
# otherwise.
#
#   mimalloc  (default) fetch and build mimalloc, and link it
#   tcmalloc            link the system gperftools tcmalloc, if it can be found
#   system              plain malloc from the C library
set(STP_ALLOCATOR "mimalloc" CACHE STRING
    "Memory allocator to link against (mimalloc/tcmalloc/system)")
set_property(CACHE STP_ALLOCATOR PROPERTY STRINGS mimalloc tcmalloc system)

# Back-compat: -DUSE_TCMALLOC=ON/OFF predates STP_ALLOCATOR and still works.
if (DEFINED USE_TCMALLOC AND NOT DEFINED _STP_ALLOCATOR_FROM_USE_TCMALLOC)
    if (USE_TCMALLOC)
        message(WARNING "USE_TCMALLOC is deprecated, use -DSTP_ALLOCATOR=tcmalloc")
        set(STP_ALLOCATOR "tcmalloc" CACHE STRING "" FORCE)
    else()
        message(WARNING "USE_TCMALLOC=OFF is deprecated, use -DSTP_ALLOCATOR=system")
        set(STP_ALLOCATOR "system" CACHE STRING "" FORCE)
    endif()
    set(_STP_ALLOCATOR_FROM_USE_TCMALLOC ON CACHE INTERNAL "")
endif()

# STP_ALLOCATOR_LIBRARY is what the executables link; empty means system malloc.
set(STP_ALLOCATOR_LIBRARY "")

if (STP_ALLOCATOR STREQUAL "mimalloc")
    # Fetched, not linked, for the same reason as ABC: STP configures
    # mimalloc's build rather than consuming its output, and that needs
    # add_subdirectory().
    #
    # A hard error rather than a quiet fall back to system malloc, which the
    # documentation measures at roughly 14% slower. An allocator silently
    # changing under a build is exactly the kind of thing nobody notices until
    # a benchmark disagrees with the last one.
    if (NOT DEFINED FETCHCONTENT_SOURCE_DIR_MIMALLOC AND NOT ENABLE_AUTO_DOWNLOAD)
        message(FATAL_ERROR
            "STP_ALLOCATOR is mimalloc, which has to be fetched. Configure "
            "with -DENABLE_AUTO_DOWNLOAD=ON to have it cloned here, point "
            "-DFETCHCONTENT_SOURCE_DIR_MIMALLOC at an existing checkout, or "
            "choose another allocator with -DSTP_ALLOCATOR=tcmalloc or "
            "-DSTP_ALLOCATOR=system (the last is about 14% slower).")
    endif()
    # The static library is what the executables link: it keeps them
    # self-contained, with nothing extra to install or ship. The shared one is
    # built too but not installed - it is there to be LD_PRELOADed by processes
    # that embed libstp rather than run the stp binary, the Python (ctypes)
    # interface being the one in tree. See tests/api/python/allocator_tests.py.
    set(MI_BUILD_SHARED ON  CACHE BOOL "" FORCE)
    set(MI_BUILD_OBJECT OFF CACHE BOOL "" FORCE)
    set(MI_BUILD_TESTS  OFF CACHE BOOL "" FORCE)
    set(MI_BUILD_STATIC ON  CACHE BOOL "" FORCE)
    set(MI_OVERRIDE     ON  CACHE BOOL "" FORCE)
    # SOURCE_SUBDIR names a directory mimalloc has not got, so MakeAvailable
    # populates without calling add_subdirectory(): this one needs
    # EXCLUDE_FROM_ALL, which MakeAvailable could not be told until CMake 3.28.
    FetchContent_Declare(
        mimalloc
        GIT_REPOSITORY https://github.com/microsoft/mimalloc.git
        GIT_TAG 30ac9d56b8b9ea57ae84bc8ef17ef39000da08fe  # v2.4.1
        SOURCE_SUBDIR stp-adds-this-subdirectory-itself
    )
    FetchContent_MakeAvailable(mimalloc)
    add_subdirectory(${mimalloc_SOURCE_DIR} ${mimalloc_BINARY_DIR} EXCLUDE_FROM_ALL)
    # Vendored upstream code whose warnings we do not control.
    if (WERROR AND NOT MSVC)
        target_compile_options(mimalloc-static PRIVATE -Wno-error)
        target_compile_options(mimalloc PRIVATE -Wno-error)
    endif()
    set(STP_ALLOCATOR_LIBRARY mimalloc-static)
    # EXCLUDE_FROM_ALL above keeps mimalloc's other targets out of the build;
    # the shared library is small and wanted by anyone preloading it, so opt it
    # back in.
    set_target_properties(mimalloc PROPERTIES EXCLUDE_FROM_ALL FALSE)
    set(STP_ALLOCATOR_PRELOADABLE mimalloc)
    message(STATUS "Allocator: mimalloc (${mimalloc_SOURCE_DIR})")

elseif (STP_ALLOCATOR STREQUAL "tcmalloc")
    if (NOT BUILD_SHARED_LIBS)
        # A -static link needs the archive; a versioned .so is useless here.
        find_library(TCMALLOC_LIBRARY NAMES tcmalloc_minimal tcmalloc)
    else()
        # Distributions ship the unversioned symlink only in the -dev package,
        # so also accept the runtime soname that everyone actually has.
        find_library(TCMALLOC_LIBRARY
                     NAMES tcmalloc_minimal tcmalloc
                           libtcmalloc_minimal.so.4 libtcmalloc.so.4)
    endif()
    if (NOT TCMALLOC_LIBRARY)
        message(FATAL_ERROR "STP_ALLOCATOR=tcmalloc but tcmalloc was not found. "
                "Install gperftools (e.g. libtcmalloc-minimal-dev / gperftools-devel), "
                "point -DTCMALLOC_LIBRARY at it, or use -DSTP_ALLOCATOR=mimalloc.")
    endif()
    set(STP_ALLOCATOR_LIBRARY ${TCMALLOC_LIBRARY})
    message(STATUS "Allocator: tcmalloc (${TCMALLOC_LIBRARY})")

elseif (STP_ALLOCATOR STREQUAL "system")
    message(STATUS "Allocator: system malloc (slower; -DSTP_ALLOCATOR=mimalloc is the default)")

else()
    message(FATAL_ERROR "STP_ALLOCATOR must be mimalloc, tcmalloc or system, "
            "not '${STP_ALLOCATOR}'")
endif()

add_feature_info(Allocator "NOT STP_ALLOCATOR STREQUAL system"
                 "Links ${STP_ALLOCATOR} for faster allocation")

# -----------------------------------------------------------------------------
# Find CryptoMiniSat
# -----------------------------------------------------------------------------
# Three-valued, because "use CryptoMiniSat" has three answers and this used to
# need three variables to say them:
#
#   OFF   (default) do not look for it              (was -DNOCRYPTOMINISAT=ON)
#   ON    it is required; fail if it is missing     (was -DFORCE_CMS=ON)
#   AUTO  use it if it happens to be installed      (was the old default)
#
# The default is OFF, and that is the change: CryptoMiniSat used to be linked
# in whenever it happened to be installed. A build whose set of SAT backends
# depends on what the machine has lying around cannot be reproduced from its
# flags, which is most of what moving the dependencies to a declared,
# downloadable set is for. AUTO is still there for anyone who wants the old
# behaviour by name.
set(CMS_OPTION_DOC "Use the CryptoMiniSat solver backend: ON requires it, OFF never uses it, AUTO uses it if installed")
set(USE_CRYPTOMINISAT "OFF" CACHE STRING "${CMS_OPTION_DOC}")
set_property(CACHE USE_CRYPTOMINISAT PROPERTY STRINGS OFF ON AUTO)

# Back-compat for the two variables this replaces. Both are still accepted and
# still mean what they meant -- including NOCRYPTOMINISAT=OFF, which meant "do
# look for it", and so translates to AUTO rather than to ON. Translated once
# and then remembered, the way USE_TCMALLOC -> STP_ALLOCATOR is below: a
# deprecated name left sitting in a build directory's cache must not go on
# overruling a later -DUSE_CRYPTOMINISAT=, and the warning should be seen once
# rather than on every reconfigure.
if (NOT DEFINED _STP_CMS_FROM_LEGACY_OPTION)
    if (DEFINED FORCE_CMS AND FORCE_CMS)
        message(WARNING "FORCE_CMS is deprecated, use -DUSE_CRYPTOMINISAT=ON")
        set(USE_CRYPTOMINISAT ON CACHE STRING "${CMS_OPTION_DOC}" FORCE)
        set(_STP_CMS_FROM_LEGACY_OPTION ON CACHE INTERNAL "")
    elseif (DEFINED NOCRYPTOMINISAT)
        if (NOCRYPTOMINISAT)
            message(WARNING "NOCRYPTOMINISAT is deprecated, use -DUSE_CRYPTOMINISAT=OFF")
            set(USE_CRYPTOMINISAT OFF CACHE STRING "${CMS_OPTION_DOC}" FORCE)
        else()
            message(WARNING "NOCRYPTOMINISAT=OFF is deprecated, use -DUSE_CRYPTOMINISAT=AUTO")
            set(USE_CRYPTOMINISAT AUTO CACHE STRING "${CMS_OPTION_DOC}" FORCE)
        endif()
        set(_STP_CMS_FROM_LEGACY_OPTION ON CACHE INTERNAL "")
    endif()
endif()

if (NOT USE_CRYPTOMINISAT MATCHES "^(ON|OFF|AUTO)$")
    message(FATAL_ERROR "USE_CRYPTOMINISAT must be ON, OFF or AUTO, not "
            "'${USE_CRYPTOMINISAT}'")
endif()

# Asked for by name, or merely not refused? The two differ only when the lookup
# fails: an explicit ON is a configuration error, AUTO is not.
if (USE_CRYPTOMINISAT STREQUAL "ON")
    set(CMS_EXPLICITLY_REQUESTED TRUE)
else()
    set(CMS_EXPLICITLY_REQUESTED FALSE)
endif()

if (NOT USE_CRYPTOMINISAT STREQUAL "OFF")
  # REQUIRED only when it was asked for by name: an explicit ON makes a missing
  # CryptoMiniSat a configuration error, while leaving the option unset means
  # "use it if it is there". cmake/FindCryptoMiniSat.cmake carries the GMP
  # warning, the cadical/cadiback preamble and the reason it is the one
  # dependency STP does not build for you.
  # 5.11 is the floor, and it is chosen from evidence rather than taste: it is
  # the oldest release anything in this repository builds -- the Dockerfiles do
  # -- and every method lib/Sat/CryptoMinisat5.cpp calls exists in it. Nothing
  # here builds anything older, so nothing here can say an older one works.
  if (CMS_EXPLICITLY_REQUESTED)
      find_package(CryptoMiniSat 5.11 REQUIRED)
  else()
      find_package(CryptoMiniSat 5.11)
  endif()
  # HAVE_FLAG_STD_CPP11 is in the condition because CryptoMiniSat's headers are
  # C++11: a compiler that cannot be told to accept them cannot compile against
  # it whether or not the package was found.
  if (CryptoMiniSat_FOUND AND HAVE_FLAG_STD_CPP11)
    add_definitions(-DUSE_CRYPTOMINISAT)
    set(USE_CRYPTOMINISAT ON)
  else()
    set(USE_CRYPTOMINISAT OFF)
  endif()
else()
  set(USE_CRYPTOMINISAT OFF)
endif()
add_feature_info(CryptoMiniSat USE_CRYPTOMINISAT "Enables CryptoMiniSat solver, allows --cryptominisat5 option")

# CryptoMiniSat >= 5.14 builds its own CaDiCaL -- the meelgroup fork, 2.1.3 as
# of 5.14.7 -- and installs it beside itself, exported as an imported target
# named plainly `cadical`. cryptominisat5Targets.cmake then requires a target
# by that name to exist, which is why the block above has to find_package it.
#
# When libcryptominisat5 is static, that target is part of its link interface:
# a consumer has to resolve a static library's private dependencies itself, so
# both CaDiCaLs reach libstp's link line and their symbols collide. Neither
# target can be renamed, so refuse the combination here. Left to the linker it
# surfaces as pages of duplicate definitions that never mention CryptoMiniSat.
#
# A shared libcryptominisat5 is fine and is not rejected: CMake resolves its
# private dependencies inside the .so, which exports no CaDiCaL symbols at all,
# so only the CaDiCaL that CADICAL_DIR names is ever linked or called.
if (USE_CADICAL AND USE_CRYPTOMINISAT AND TARGET cryptominisat5 AND TARGET cadical)
    get_target_property(_cms_type cryptominisat5 TYPE)
    if (_cms_type STREQUAL "STATIC_LIBRARY")
        get_target_property(_cms_cadical cadical IMPORTED_LOCATION_RELEASE)
        if (NOT _cms_cadical)
            get_target_property(_cms_cadical cadical IMPORTED_LOCATION)
        endif()
        if (NOT _cms_cadical)
            set(_cms_cadical "the copy in CryptoMiniSat's install prefix")
        endif()
        message(FATAL_ERROR
            "A static CryptoMiniSat cannot be combined with USE_CADICAL. Both "
            "put a CaDiCaL on libstp's link line and their symbols collide:\n"
            "    CryptoMiniSat's bundled CaDiCaL: ${_cms_cadical}\n"
            "    CADICAL_DIR's CaDiCaL:           ${CADICAL_LIBRARY}\n"
            "Either build CryptoMiniSat as a shared library "
            "(scripts/deps/setup-cms.sh -DBUILD_SHARED_LIBS=ON), which keeps "
            "its bundled CaDiCaL to itself, or leave CryptoMiniSat out with "
            "-DUSE_CRYPTOMINISAT=OFF.")
    endif()
endif()

# -----------------------------------------------------------------------------
# Every backend is optional, but a solver with no SAT backend at all cannot
# solve anything, so insist that at least one made it in.
#
# This is the point at which all four are settled: USE_MINISAT, USE_CADICAL and
# USE_RISS are plain options decided above, and USE_CRYPTOMINISAT has just been
# resolved from its three-valued form to a definite ON or OFF. Asking here,
# rather than after MiniSat has been searched for, means the answer arrives
# before any of the per-backend lookups spend time or produce their own errors.
# -----------------------------------------------------------------------------
if (NOT USE_MINISAT AND NOT USE_CRYPTOMINISAT AND NOT USE_CADICAL AND NOT USE_RISS)
    message(FATAL_ERROR
            "No SAT backend is enabled, so this build could not solve "
            "anything. Enable at least one of:\n"
            "    -DUSE_CADICAL=ON -DCADICAL_DIR=<checkout>  (see scripts/deps/setup-cadical.sh)\n"
            "    -DUSE_CRYPTOMINISAT=ON                     (must already be installed)\n"
            "    -DUSE_MINISAT=ON\n"
            "    -DUSE_RISS=ON -DRISS_DIR=<checkout>")
endif()

# ----------
# manpage
# ----------
# Three-valued, because whether stp.1 is built and installed used to be decided
# entirely by whether help2man happened to be on the build machine. That made
# the contents of an install depend on something nobody had asked for and which
# did not appear in the feature summary -- awkward for a packager, who wants
# either a guarantee the page is there or a guarantee it is not.
#
#   IGNORE  build it if help2man is available          (the historical default)
#   ON      build it; fail configure if help2man is missing
#   OFF     never build it
stp_option(BUILD_MANPAGE "Build and install the stp(1) manpage with help2man")

if (NOT ${CMAKE_SYSTEM_NAME} MATCHES "Linux")
    # help2man runs the binary it documents, so it is not something to attempt
    # when the build may not be able to run its own output.
    if (BUILD_MANPAGE)
        message(FATAL_ERROR "BUILD_MANPAGE is ON but the manpage is only built on Linux")
    endif()
    set(BUILD_MANPAGE OFF)
    message(STATUS "Not on Linux, not creating manpage")
elseif (NOT BUILD_EXECUTABLES)
    # There is no stp binary to extract --help from.
    if (BUILD_MANPAGE)
        message(FATAL_ERROR "BUILD_MANPAGE is ON but BUILD_EXECUTABLES is OFF, "
                            "so there is no stp binary to document")
    endif()
    set(BUILD_MANPAGE OFF)
elseif (NOT BUILD_MANPAGE STREQUAL "OFF")
    find_program(HELP2MAN_FOUND help2man)
    if (HELP2MAN_FOUND)
        set(BUILD_MANPAGE ON)
    elseif (BUILD_MANPAGE)
        message(FATAL_ERROR "BUILD_MANPAGE is ON but help2man was not found. "
                            "Install help2man, or configure with -DBUILD_MANPAGE=OFF.")
    else()
        set(BUILD_MANPAGE OFF)
        message(STATUS "Cannot find help2man, not creating manpage")
    endif()
else()
    set(BUILD_MANPAGE OFF)
endif()

if (BUILD_MANPAGE)
    ADD_CUSTOM_TARGET(man_stp
        ALL
        DEPENDS stp-bin
    )

    ADD_CUSTOM_COMMAND(
        TARGET man_stp
        COMMAND help2man
        ARGS  --name="Simple Theorem Prover SMT solver" --version-string=${STP_FULL_VERSION} --help-option="--help" $<TARGET_FILE:stp-bin> -o ${CMAKE_CURRENT_BINARY_DIR}/stp.1
    )

    INSTALL(
        FILES ${CMAKE_CURRENT_BINARY_DIR}/stp.1
        DESTINATION ${CMAKE_INSTALL_PREFIX}/man/man1)
    message(STATUS "Manpage will be created and installed")
endif()
add_feature_info(Manpage BUILD_MANPAGE "Builds and installs the stp(1) manpage")


# -----------------------------------------------------------------------------
# Find Minisat
# -----------------------------------------------------------------------------

if (USE_MINISAT)
    # MINISAT_INCLUDE_DIRS and MINISAT_LIBDIR still name a MiniSat that was
    # built but not installed, and zlib is still required -- both now live in
    # cmake/FindMiniSat.cmake, along with the ability to build one.
    find_package(MiniSat REQUIRED)
    add_definitions(-DUSE_MINISAT)
    # The include directory is no longer added project-wide: the MiniSat target
    # carries it to lib/Sat and lib/Incremental, which are the two object
    # libraries whose sources reach a MiniSat header, and to the unit tests
    # through AddSTPGTest. (There used to be a `set(LIBS ...)` here too, whose
    # value nothing ever read.)
endif()

# -----------------------------------------------------------------------------
# Find Parser and Lexer generators
# -----------------------------------------------------------------------------

# On macOS, search Homebrew for keg-only versions of Bison and Flex. Xcode does
# not provide new enough versions for us to use.
if (CMAKE_HOST_SYSTEM_NAME MATCHES "Darwin")
    execute_process(
        COMMAND brew --prefix bison 
        RESULT_VARIABLE BREW_BISON
        OUTPUT_VARIABLE BREW_BISON_PREFIX
        OUTPUT_STRIP_TRAILING_WHITESPACE
    )
    if (BREW_BISON EQUAL 0 AND EXISTS "${BREW_BISON_PREFIX}")
        message(STATUS "Found Bison keg installed by Homebrew at ${BREW_BISON_PREFIX}")
        set(BISON_EXECUTABLE "${BREW_BISON_PREFIX}/bin/bison")
    endif()
    
    execute_process(
        COMMAND brew --prefix flex 
        RESULT_VARIABLE BREW_FLEX
        OUTPUT_VARIABLE BREW_FLEX_PREFIX
        OUTPUT_STRIP_TRAILING_WHITESPACE
    )
    if (BREW_FLEX EQUAL 0 AND EXISTS "${BREW_FLEX_PREFIX}")
        message(STATUS "Found Flex keg installed by Homebrew at ${BREW_FLEX_PREFIX}")
        set(FLEX_EXECUTABLE "${BREW_FLEX_PREFIX}/bin/flex")
    endif()
endif()


find_package(BISON REQUIRED)
find_package(FLEX REQUIRED)

if (BISON_VERSION VERSION_LESS "2.6")
    message(FATAL_ERROR "STP requires Bison 2.6 or newer")
endif()

# -----------------------------------------------------------------------------
# Floating-point support (uses the header-only SymFPU library)
# -----------------------------------------------------------------------------
# Required: every build of STP solves the SMT-LIB floating-point theory.
# SYMFPU_INCLUDE_DIRS still names a directory containing a symfpu clone, and
# cmake/FindSymFPU.cmake can fetch and patch one otherwise.
find_package(SymFPU REQUIRED)

# LibBF folds the real literals in floating-point input -- ((_ to_fp 8 24)
# RNE 1.5) -- to their exactly-rounded bits while parsing. It is required, and
# with -DENABLE_AUTO_DOWNLOAD=ON it does not have to be installed: see
# cmake/FindLibBF.cmake.
find_package(LibBF REQUIRED)

# The shared dependency directory, if there is one, now holds whatever this
# configure decided to build. Check it was not filled by an incompatible build.
stp_check_dep_dir_config()

# -----------------------------------------------------------------------------
# Query definitions
# -----------------------------------------------------------------------------
get_directory_property( DirDefs DIRECTORY ${CMAKE_SOURCE_DIR} COMPILE_DEFINITIONS )
set(COMPILE_DEFINES)
foreach( d ${DirDefs} )
    # message( STATUS "Found Define: " ${d} )
    set(COMPILE_DEFINES "${COMPILE_DEFINES} -D${d}")
endforeach()
message(STATUS "All defines at startup: ${COMPILE_DEFINES}")

# -----------------------------------------------------------------------------
# Setup library build path (this is **not** the library install path)
# -----------------------------------------------------------------------------
if(WIN32)
  # Create a single bin/ output directory so that DLL files can be
  # readily found on DLL platforms.
  set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${PROJECT_BINARY_DIR}/bin)
  set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${PROJECT_BINARY_DIR}/bin)
  set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${PROJECT_BINARY_DIR}/bin)
endif()

if(DEFINED CMAKE_CONFIGURATION_TYPES)
  # Placing the binaries in ${CMAKE_*_OUTPUT_DIRECTORY} without regard to
  # the debug/release/... configuration. This is needed for build systems
  # where files for multiple configurations are kept within the same build
  # directory (eg. MSBuild), since some targets (e.g. python-interface-tests)
  # require the path to the stp library to be given in a configuration file.
  # Note: the paths could be determined in a cleaner fashion by using generator
  # expressions, which were used up to commit 1af1f5. However, that solution
  # was not feasible, since CMake versions provided by recent Debian versions
  # are buggy w.r.t. generator expressions.
  foreach(OUTPUTCONFIG ${CMAKE_CONFIGURATION_TYPES})
    string(TOUPPER ${OUTPUTCONFIG} OUTPUTCONFIG_UPPER)
    set(CMAKE_RUNTIME_OUTPUT_DIRECTORY_${OUTPUTCONFIG_UPPER} ${CMAKE_RUNTIME_OUTPUT_DIRECTORY})
    set(CMAKE_LIBRARY_OUTPUT_DIRECTORY_${OUTPUTCONFIG_UPPER} ${CMAKE_LIBRARY_OUTPUT_DIRECTORY})
    set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY_${OUTPUTCONFIG_UPPER} ${CMAKE_ARCHIVE_OUTPUT_DIRECTORY})
  endforeach(OUTPUTCONFIG CMAKE_CONFIGURATION_TYPES)
else()
  set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${PROJECT_BINARY_DIR}/lib)
  set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${PROJECT_BINARY_DIR}/lib)
endif()

# -----------------------------------------------------------------------------
# Provide an export name to be used by targets that wish to export themselves.
# -----------------------------------------------------------------------------
set(STP_EXPORT_NAME "STPTargets")

# Tests which exercise the staged install tree are configured before the
# install rules below.  Publish the package location now so those tests and
# the eventual install(EXPORT) use the same cache-controlled destination.
if(WIN32 AND NOT CYGWIN)
  set(DEF_INSTALL_CMAKE_DIR CMake)
else()
  set(DEF_INSTALL_CMAKE_DIR ${CMAKE_INSTALL_LIBDIR}/cmake/STP)
endif()
set(STP_INSTALL_CMAKE_DIR ${DEF_INSTALL_CMAKE_DIR} CACHE PATH
  "Installation directory for STP CMake files"
)

# -----------------------------------------------------------------------------
# Testing and Python interface options
# -----------------------------------------------------------------------------

option(ENABLE_TESTING "Enable testing" OFF)

# A Python 3 interpreter is always needed: lib/AST/genkinds.py generates the
# kind tables at build time, so the search cannot be tied to the (optional)
# Python bindings. PYTHON_EXECUTABLE stays the documented way to choose the
# interpreter (the rest of the build and our CI use that name), so feed it
# to the finder and write the validated result back to it.
set(PYTHON_DOC_STRING "Python 3 interpreter for the code generator, the bindings and the test suite")
if(CMAKE_VERSION VERSION_LESS 3.12)
    # FindPython3 arrived in CMake 3.12; on older CMake ask the deprecated
    # module for a Python 3 interpreter instead. It searches PYTHON_EXECUTABLE
    # directly, so no hint needs forwarding.
    find_package(PythonInterp 3)
    set(Python3_EXECUTABLE "${PYTHON_EXECUTABLE}")
    set(Python3_Interpreter_FOUND ${PYTHONINTERP_FOUND})
else()
    if(PYTHON_EXECUTABLE)
        set(Python3_EXECUTABLE "${PYTHON_EXECUTABLE}" CACHE FILEPATH
            "${PYTHON_DOC_STRING}" FORCE)
    endif()
    find_package(Python3 COMPONENTS Interpreter)
endif()

# Publish the result in the cache so that subprojects looking for an
# interpreter of their own (e.g. gtest, which still uses the deprecated
# FindPythonInterp) pick up this Python 3 rather than finding a Python 2.
if(Python3_Interpreter_FOUND)
    set(PYTHON_EXECUTABLE "${Python3_EXECUTABLE}" CACHE FILEPATH
        "${PYTHON_DOC_STRING}" FORCE)
else()
    set(PYTHON_EXECUTABLE "" CACHE FILEPATH "${PYTHON_DOC_STRING}" FORCE)
    # Don't let a rejected interpreter stick in the cache, or every later
    # reconfigure would keep re-testing the same unsuitable one.
    unset(Python3_EXECUTABLE CACHE)
    message(FATAL_ERROR
        "STP requires a Python 3 interpreter to generate lib/AST/ASTKind.{h,cpp}. "
        "Install python3, or point -DPYTHON_EXECUTABLE=<path> at one.")
endif()

# The Python bindings are a separate, optional matter: they additionally need
# a shared library to bind against.
if((NOT DEFINED ENABLE_PYTHON_INTERFACE) OR ENABLE_PYTHON_INTERFACE)
    if(BUILD_SHARED_LIBS)
        set(ENABLE_PYTHON_INTERFACE ON)
    else()
        set(ENABLE_PYTHON_INTERFACE OFF)
    endif()
endif()
add_feature_info(PythonInterface ENABLE_PYTHON_INTERFACE "Enables Python interface")

# -----------------------------------------------------------------------------
# Compile all subdirs
# -----------------------------------------------------------------------------

message(STATUS "Final CXX flags ${CMAKE_CXX_FLAGS}")

add_subdirectory(lib)

# Only tools/stp/main.cpp includes CLI11, so it is looked for only when there
# is a binary to build.
if (BUILD_EXECUTABLES)
    find_package(CLI11 REQUIRED)
endif()
add_subdirectory(tools)
add_subdirectory(bindings)
add_feature_info(Executables BUILD_EXECUTABLES "Enables executables compilation")

# -----------------------------------------------------------------------------
# Add uninstall target for makefiles
# -----------------------------------------------------------------------------
configure_file(
  "${CMAKE_CURRENT_SOURCE_DIR}/cmake/modules/cmake_uninstall.cmake.in"
  "${CMAKE_CURRENT_BINARY_DIR}/cmake_uninstall.cmake"
  IMMEDIATE @ONLY
)

add_custom_target(uninstall
  COMMAND ${CMAKE_COMMAND} -P ${CMAKE_CURRENT_BINARY_DIR}/cmake_uninstall.cmake
)

# -----------------------------------------------------------------------------
# Add tests if required
# -----------------------------------------------------------------------------

if(ENABLE_TESTING AND NOT PYTHON_EXECUTABLE)
    message(STATUS "Python interpreter cannot be found. Please install it to have the python interface and to enable testing")
    set(ENABLE_TESTING OFF)
endif()

if(ENABLE_TESTING)
    if (NOT BUILD_SHARED_LIBS)
        set(ENABLE_TESTING OFF)
    endif()
endif()

if(ENABLE_TESTING)
  enable_testing()
  set(UNIT_TEST_EXE_SUFFIX "Tests" CACHE STRING "Suffix for Unit test executable")
#   add_custom_target(check
#     COMMENT "top level target to invoke all other tests"
#   )

  add_subdirectory(tests)
endif()
add_feature_info(Tests ENABLE_TESTING "Enables tests")

# -----------------------------------------------------------------------------
# Print information about used features
# -----------------------------------------------------------------------------
feature_summary(WHAT ENABLED_FEATURES DISABLED_FEATURES)

# -----------------------------------------------------------------------------
# Export our targets so that other CMake based projects can interface with
# the build of STP in the build-tree
# -----------------------------------------------------------------------------
set(STP_TARGETS_FILENAME "STPTargets.cmake")
set(STP_CONFIG_FILENAME "STPConfig.cmake")
set(STP_CONFIG_VERSION_FILENAME "STPConfigVersion.cmake")

export(TARGETS stp
    FILE "${PROJECT_BINARY_DIR}/${STP_TARGETS_FILENAME}")

# Create STPConfig file
set(EXPORT_TYPE "Build-tree")
set(CONF_INCLUDE_DIRS "${PROJECT_BINARY_DIR}/include")
configure_file(STPConfig.cmake.in
  "${PROJECT_BINARY_DIR}/${STP_CONFIG_FILENAME}" @ONLY
)
configure_file(STPConfigVersion.cmake.in
  "${PROJECT_BINARY_DIR}/${STP_CONFIG_VERSION_FILENAME}" @ONLY
)

# Export this package to the CMake user package registry
# Now the user can just use find_package(STP) on their system
export(PACKAGE STP)


# -----------------------------------------------------------------------------
# Install the licences
# -----------------------------------------------------------------------------
# STP's own licence, and the notices of the third-party code compiled into it.
# Several of those -- ABC, mimalloc, ankerl::unordered_dense, LibBF -- are MIT
# or BSD, whose one condition is that the notice travels with the binary, so an
# install that left these behind would not meet it. Which components are
# actually linked in varies with the configuration, and the file says which
# ones are conditional, so it is installed whole rather than assembled per
# build.
install(FILES
  "${PROJECT_SOURCE_DIR}/LICENSE"
  "${PROJECT_SOURCE_DIR}/LICENSE_COMPONENTS"
  DESTINATION "${CMAKE_INSTALL_DOCDIR}"
)

# -----------------------------------------------------------------------------
# Export our targets so that other CMake based projects can interface with
# the build of STP that is installed.
# -----------------------------------------------------------------------------
# Create STPConfig file
set(EXPORT_TYPE "installed")
set(CONF_INCLUDE_DIRS "${CMAKE_INSTALL_FULL_INCLUDEDIR}")
configure_file(STPConfig.cmake.in
  "${PROJECT_BINARY_DIR}/${CMAKE_FILES_DIRECTORY}/${STP_CONFIG_FILENAME}" @ONLY
)

install(FILES
  "${PROJECT_BINARY_DIR}/${CMAKE_FILES_DIRECTORY}/${STP_CONFIG_FILENAME}"
  "${PROJECT_BINARY_DIR}/${STP_CONFIG_VERSION_FILENAME}"
  DESTINATION "${STP_INSTALL_CMAKE_DIR}"
)

# Install the export set for use with the install-tree
install(EXPORT ${STP_EXPORT_NAME} DESTINATION
  "${STP_INSTALL_CMAKE_DIR}"
)
