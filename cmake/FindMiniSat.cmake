# AUTHORS: Dan Liew, Ryan Govostes, Mate Soos, Andrew Teylu
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

# Find MiniSat, the optional -DUSE_MINISAT backend.
#
#   MiniSat          imported target, carrying the headers, the archive and zlib
#   MINISAT_INCLUDE_DIRS / MINISAT_LIBRARIES   what the target was built from
#
# MINISAT_INCLUDE_DIRS and MINISAT_LIBDIR are also *inputs*, and are the
# documented way to name a MiniSat that was built but not installed. That is
# rung 0 of the ladder in cmake/deps-helper.cmake.

include(deps-helper)

# MiniSat reads gzipped DIMACS, and says so in its public headers: anything
# that includes minisat/core/Solver.h needs zlib.h on its include path too.
# REQUIRED, because a MiniSat build without it cannot compile at all -- left
# unqualified, the failure used to arrive minutes later from inside a MiniSat
# header, with nothing to connect it to the lookup that had quietly failed.
find_package(ZLIB REQUIRED)

set(MiniSat_FOUND_SYSTEM FALSE)

if(MINISAT_INCLUDE_DIRS OR MINISAT_LIBDIR)
    # Rung 0. NO_DEFAULT_PATH so that what the caller named is what is used:
    # STP_DEP_DIR and deps/install are on CMAKE_PREFIX_PATH, which find_library
    # reaches before HINTS, so a HINTS lookup could resolve to a MiniSat other
    # than the one asked for. This is the same trap the CADICAL_DIR note in the
    # top-level CMakeLists describes, avoided the same way.
    #
    # MINISAT_LIBDIR may name either a build directory or an install prefix, so
    # look in it and in its lib/ -- the Windows CI job passes an install prefix.
    find_path(MINISAT_INCLUDE_DIR NAMES minisat/core/Solver.h
              PATHS ${MINISAT_INCLUDE_DIRS} NO_DEFAULT_PATH)
    find_library(MINISAT_LIBRARY NAMES minisat minisat2
                 PATHS ${MINISAT_LIBDIR} ${MINISAT_LIBDIR}/lib
                       ${MINISAT_LIBRARY_DIRS} NO_DEFAULT_PATH)
    if(NOT MINISAT_INCLUDE_DIR OR NOT MINISAT_LIBRARY)
        message(FATAL_ERROR
            "MINISAT_INCLUDE_DIRS or MINISAT_LIBDIR was set, but no MiniSat "
            "was found through them:\n"
            "    minisat/core/Solver.h under: ${MINISAT_INCLUDE_DIRS}\n"
            "    a minisat library under:     ${MINISAT_LIBDIR}\n"
            "Correct them, or unset both to search the system instead.")
    endif()
    set(MiniSat_FOUND_SYSTEM TRUE)
else()
    # Rung 1. Includes anything installed into STP_DEP_DIR by another build
    # directory.
    find_path(MINISAT_INCLUDE_DIR NAMES minisat/core/Solver.h
              PATH_SUFFIXES minisat minisat2)
    find_library(MINISAT_LIBRARY NAMES minisat minisat2)
    if(MINISAT_INCLUDE_DIR AND MINISAT_LIBRARY)
        set(MiniSat_FOUND_SYSTEM TRUE)
    endif()
endif()

if(NOT MiniSat_FOUND_SYSTEM)
    # Rungs 2 and 3.
    check_ep_downloaded("MiniSat-EP")
    if(NOT MiniSat-EP_DOWNLOADED)
        check_auto_download("MiniSat" "-DUSE_MINISAT=OFF")
    endif()

    # STP maintains a fork: upstream MiniSat 2.2 has not moved since 2010 and
    # does not build with a current compiler. A commit rather than a tag,
    # because stp/minisat carries only the upstream 2.0/2.2.x release tags,
    # none of which name the fork's own history.
    set(MiniSat_VERSION "74c4aa2e450ef4eb6eb159e984d64d86a2a35058")

    set(MiniSat_ARCHIVE
        "${CMAKE_STATIC_LIBRARY_PREFIX}minisat${CMAKE_STATIC_LIBRARY_SUFFIX}")

    ExternalProject_Add(
        MiniSat-EP
        ${STP_EP_COMMON_CONFIG}
        GIT_REPOSITORY https://github.com/stp/minisat
        GIT_TAG ${MiniSat_VERSION}
        CMAKE_ARGS ${STP_EP_COMMON_CMAKE_ARGS}
                   -DCMAKE_INSTALL_PREFIX=<INSTALL_DIR>
                   -DCMAKE_INSTALL_LIBDIR=lib
                   # The archive is linked into libstp, so that an installed
                   # STP does not depend on a libminisat.so living inside a
                   # build tree. STP_EP_COMMON_CMAKE_ARGS supplies the -fPIC
                   # this then needs; MiniSat's own CMake never sets it.
                   -DSTATICCOMPILE=ON
        # Only the library. MiniSat also builds two command-line programs that
        # STP never runs, and STATICCOMPILE puts -static on them, which needs a
        # static libz, libstdc++ and libc on the build machine -- a requirement
        # STP has no business imposing, and one a distribution that ships no
        # libz.a cannot meet at all.
        BUILD_COMMAND ${CMAKE_COMMAND} --build . --config ${CMAKE_BUILD_TYPE}
                      --target minisat
        # ...which means upstream's install rule, which names those programs
        # too, cannot be used either.
        INSTALL_COMMAND ${CMAKE_COMMAND}
                        -DSRC=<SOURCE_DIR> -DBIN=<BINARY_DIR>
                        -DDST=<INSTALL_DIR> -DLIBNAME=${MiniSat_ARCHIVE}
                        -P "${CMAKE_CURRENT_LIST_DIR}/deps-utils/minisat-install.cmake"
        BUILD_BYPRODUCTS <INSTALL_DIR>/lib/${MiniSat_ARCHIVE}
    )
    add_dependencies(deps MiniSat-EP)

    set(MINISAT_INCLUDE_DIR "${STP_DEP_DIR}/include")
    set(MINISAT_LIBRARY "${STP_DEP_DIR}/lib/${MiniSat_ARCHIVE}")
endif()

set(MiniSat_FOUND TRUE)

# The names the rest of the build already uses.
set(MINISAT_INCLUDE_DIRS ${MINISAT_INCLUDE_DIR})
set(MINISAT_LIBRARIES ${MINISAT_LIBRARY})

# SYSTEM: MiniSat is upstream code whose warnings STP does not control, and a
# WERROR build compiles its headers as part of every translation unit that
# includes them. zlib travels in the link interface because MiniSat's public
# headers include zlib.h, so anything compiling against MiniSat needs it too.
add_library(MiniSat UNKNOWN IMPORTED GLOBAL)
set_target_properties(MiniSat PROPERTIES
    IMPORTED_LOCATION "${MINISAT_LIBRARY}"
    INTERFACE_INCLUDE_DIRECTORIES "${MINISAT_INCLUDE_DIR}"
    INTERFACE_SYSTEM_INCLUDE_DIRECTORIES "${MINISAT_INCLUDE_DIR}"
    INTERFACE_LINK_LIBRARIES ZLIB::ZLIB
)

# Whether this MiniSat lets a caller stop a search already in progress.
#
# MiniSat counts work, not time, so a wall-clock budget can only be enforced
# between calls into it unless something can end a search from outside. The
# terminator hook that allows it is recent, and a distribution's MiniSat will
# not have it -- so decide rather than require, and fall back to the older
# behaviour where it is absent.
if(NOT DEFINED MINISAT_HAS_TERMINATOR)
    if(MiniSat_FOUND_SYSTEM)
        # Somebody else's MiniSat: ask it.
        set(_term_src "${PROJECT_BINARY_DIR}/MiniSat_terminator.cpp")
        file(WRITE "${_term_src}"
             "#include <minisat/core/Solver.h>\n"
             "struct T : public Minisat::Terminator { bool terminate() { return false; } };\n"
             "int main() { Minisat::Solver s; T t; s.connectTerminator(&t); return 0; }\n")
        try_compile(MINISAT_HAS_TERMINATOR
                    "${PROJECT_BINARY_DIR}" "${_term_src}"
                    CMAKE_FLAGS "-DINCLUDE_DIRECTORIES=${MINISAT_INCLUDE_DIR}"
                    LINK_LIBRARIES ${MINISAT_LIBRARY} ZLIB::ZLIB)
    else()
        # One this build is about to fetch at MiniSat_VERSION, which carries the
        # hook. It cannot be probed: the ExternalProject builds during the build
        # phase, so at configure time there is no header to compile against and
        # a probe here answers "no" for the very MiniSat that was pinned for
        # having it. Derived from the pin, as CaDiCaL's feature gates are
        # derived from its tag.
        set(MINISAT_HAS_TERMINATOR TRUE)
    endif()
endif()

if(MINISAT_HAS_TERMINATOR)
    message(STATUS "MiniSat can be stopped mid-search: a time budget is enforced during a solve")
else()
    message(STATUS "MiniSat has no terminator hook: a time budget is only "
                   "enforced between calls into the solver")
endif()

mark_as_advanced(MINISAT_HAS_TERMINATOR)
mark_as_advanced(MiniSat_FOUND)
mark_as_advanced(MiniSat_FOUND_SYSTEM)
mark_as_advanced(MINISAT_INCLUDE_DIR)
mark_as_advanced(MINISAT_LIBRARY)

if(MiniSat_FOUND_SYSTEM)
    message(STATUS "Found MiniSat: ${MINISAT_LIBRARY}")
else()
    message(STATUS "Building MiniSat ${MiniSat_VERSION}: ${MINISAT_LIBRARY}")
    add_dependencies(MiniSat MiniSat-EP)
endif()

# EOF
