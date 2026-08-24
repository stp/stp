# AUTHORS: Andrew Teylu
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

# Find ABC, which STP uses to build AIGs and derive CNF from them. Required.
#
#   ABC              imported target, carrying the headers and the archive
#   ABC_INCLUDE_DIR / ABC_LIBRARY
#
# ABC_DIR names an existing build -- a directory holding src/ and a built
# libabc-pic -- and is rung 0 of the ladder in cmake/deps-helper.cmake.
#
# ABC used to be added with add_subdirectory(), so that STP could shadow
# BUILD_SHARED_LIBS around it and hand its targets compile options. All of that
# is expressible as arguments to a separate build, and doing it that way buys
# something add_subdirectory() cannot: ABC is 920 C files, and built here it is
# built once into STP_DEP_DIR rather than again in every build directory
# pointed at the same source.
#
# The price is that ABC is then compiled with one set of flags for all of them.
# Two things follow. Its optimisation level is whichever configuration built it
# first, which for ABC is not usually interesting. And its *defines* are not
# optional: STP's own translation units include ABC's headers, so the two must
# agree on ABC_ABI_DEFINITIONS or ABC's tagged pointers truncate on one side of
# the boundary and not the other. Those are forwarded below and recorded in the
# dependency directory's stamp, which is what makes a mismatched shared copy an
# audible warning rather than a crash in CNF generation.

include(deps-helper)

set(ABC_DIR "" CACHE PATH
    "Path to an ABC build: the directory containing src/, with a built libabc-pic beneath it")

set(ABC_FOUND_SYSTEM FALSE)

if(ABC_DIR)
    # Rung 0. NO_DEFAULT_PATH so what the caller named is what is used.
    find_path(ABC_INCLUDE_DIR NAMES aig/aig/aig.h
              PATHS ${ABC_DIR}/src ${ABC_DIR}/include NO_DEFAULT_PATH)
    find_library(ABC_LIBRARY NAMES abc-pic
                 PATHS ${ABC_DIR}/lib ${ABC_DIR}/build/lib ${ABC_DIR} NO_DEFAULT_PATH)
    if(NOT ABC_INCLUDE_DIR OR NOT ABC_LIBRARY)
        message(FATAL_ERROR
            "ABC_DIR is '${ABC_DIR}', but no ABC was found there. It should "
            "contain src/aig/aig/aig.h with a built libabc-pic beneath it.")
    endif()
    set(ABC_FOUND_SYSTEM TRUE)
else()
    # Rung 1. Nothing packages ABC this way, so in practice this finds a copy
    # another build directory installed into STP_DEP_DIR.
    find_path(ABC_INCLUDE_DIR NAMES aig/aig/aig.h)
    find_library(ABC_LIBRARY NAMES abc-pic)
    if(ABC_INCLUDE_DIR AND ABC_LIBRARY)
        set(ABC_FOUND_SYSTEM TRUE)
    endif()
endif()

if(NOT ABC_FOUND_SYSTEM)
    # Rungs 2 and 3.
    check_ep_downloaded("ABC-EP")
    if(NOT ABC-EP_DOWNLOADED)
        check_auto_download("ABC" "")
    endif()

    # stp/abc is a fork: master tracks upstream untouched and the `stp` branch
    # carries STP's changes as commits on top. To work on those, clone it and
    # point -DABC_DIR at a build of the clone. See docs/code-guide.rst.
    set(ABC_GIT_TAG "c8920763e91c5fb7427444b6cd97d580224ae88b" CACHE STRING
        "ABC revision to build when one has to be built")
    mark_as_advanced(ABC_GIT_TAG)

    set(ABC_ARCHIVE
        "${CMAKE_STATIC_LIBRARY_PREFIX}abc-pic${CMAKE_STATIC_LIBRARY_SUFFIX}")

    # -ffunction-sections -fdata-sections: so the --gc-sections on libstp can
    #   drop the ABC that nothing reaches. ABC is interconnected enough that
    #   satisfying STP's ~30 entry points pulls in most of the archive
    #   otherwise, and libstp grows from ~2MB to ~18MB.
    set(ABC_EXTRA_FLAGS "${ABC_ABI_DEFINITIONS}")
    string(REPLACE ";" " " ABC_EXTRA_FLAGS "${ABC_EXTRA_FLAGS}")
    # ABC names its own CMAKE_C_FLAGS below, which replaces the common ones, so
    # the silencing every dependency gets has to be repeated here -- on every
    # compiler, not just the ones with a -ffunction-sections to go with it.
    #
    # This wins for GCC and Clang and loses to ABC under MSVC, where it is kept
    # for the compilers it does help. ABC's CMakeLists runs ABC's Makefile to
    # recover its CFLAGS and applies them with target_compile_options, which
    # land after CMAKE_C_FLAGS; one of them is -Wall, which cl.exe accepts as a
    # spelling of /Wall, so the last word is ABC's. That is why a failing MSVC
    # dependency build is worth an uploaded log rather than the tail CMake
    # prints: the error arrives under tens of thousands of warnings.
    string(APPEND ABC_EXTRA_FLAGS " ${STP_EP_NO_WARNINGS}")
    # And for the same reason, the settings STP collected as ones every
    # dependency shares -- ABC replaces the common CMAKE_<LANG>_FLAGS, so it
    # does not receive them the way the others do. _ALLOW_KEYWORD_MACROS is in
    # here: abc_global.h defines `inline` as a macro, and ABC's one C++ file
    # then meets <xkeycheck.h>, which makes that a hard error.
    string(APPEND ABC_EXTRA_FLAGS " ${STP_EP_INHERITED_FLAGS}")
    if(NOT MSVC)
        string(APPEND ABC_EXTRA_FLAGS " -ffunction-sections -fdata-sections")
    endif()

    set(ABC_CMAKE_ARGS
        ${STP_EP_COMMON_CMAKE_ARGS}
        "-DCMAKE_C_FLAGS=${CMAKE_C_FLAGS} ${ABC_EXTRA_FLAGS}"
        "-DCMAKE_CXX_FLAGS=${CMAKE_CXX_FLAGS} ${ABC_EXTRA_FLAGS}"
        # A static archive: it is linked into libstp.so, which is
        # self-contained and installable. ABC's add_library() calls name
        # neither STATIC nor SHARED, so without this they follow
        # BUILD_SHARED_LIBS and libabc-pic becomes a 17MB shared library that
        # libstp.so records as a NEEDED entry it never installs.
        -DBUILD_SHARED_LIBS=OFF
        -DREADLINE_FOUND=FALSE
        -DABC_SKIP_TESTS=ON
        # ABC predates the minimum CMake 4 accepts by more than the common
        # arguments ask for.
        -DCMAKE_POLICY_VERSION_MINIMUM=3.5
    )
    if(CMAKE_GENERATOR_PLATFORM)
        list(APPEND ABC_CMAKE_ARGS -A "${CMAKE_GENERATOR_PLATFORM}")
    endif()
    if(CMAKE_GENERATOR_TOOLSET)
        list(APPEND ABC_CMAKE_ARGS -T "${CMAKE_GENERATOR_TOOLSET}")
    endif()

    # ABC has no CMake cache variables for these two: its CMakeLists runs ABC's
    # own Makefile to extract the source list and flags, and that Makefile
    # gates them on ifndef, which make answers from the environment. So they
    # have to be in the environment of ABC's *configure*, which means writing
    # the configure command out rather than letting CMAKE_ARGS build it.
    #
    # CUDD pulls in nine BDD modules, 123 files and ~110k lines that STP never
    # uses -- it only touches AIG construction, Dar rewriting and CNF
    # derivation. pthreads: every ABC file STP compiles that calls pthread_*
    # guards on ABC_USE_PTHREADS, and dropping it keeps the macro consistent
    # between ABC's translation units and STP's, which include ABC's headers
    # without ABC's flags.
    ExternalProject_Add(
        ABC-EP
        ${STP_EP_COMMON_CONFIG}
        GIT_REPOSITORY https://github.com/stp/abc.git
        GIT_TAG ${ABC_GIT_TAG}
        CONFIGURE_COMMAND
            ${CMAKE_COMMAND} -E env ABC_USE_NO_CUDD=1 ABC_USE_NO_PTHREADS=1
            ${CMAKE_COMMAND} -S <SOURCE_DIR> -B <BINARY_DIR>
                             -G ${CMAKE_GENERATOR} ${ABC_CMAKE_ARGS}
        # libabc-pic alone. ABC also builds a non-PIC libabc and an `abc`
        # executable that links it, which compiles the whole of ABC a second
        # time; STP links neither.
        BUILD_COMMAND ${CMAKE_COMMAND} --build <BINARY_DIR>
                      --config ${CMAKE_BUILD_TYPE} --target libabc-pic
        INSTALL_COMMAND ${CMAKE_COMMAND}
                        -DSRC=<SOURCE_DIR> -DBIN=<BINARY_DIR>
                        -DDST=<INSTALL_DIR> -DLIBNAME=${ABC_ARCHIVE}
                        -P "${CMAKE_CURRENT_LIST_DIR}/deps-utils/abc-install.cmake"
        BUILD_BYPRODUCTS <INSTALL_DIR>/lib/${ABC_ARCHIVE}
    )
    add_dependencies(deps ABC-EP)

    set(ABC_INCLUDE_DIR "${STP_DEP_DIR}/include")
    set(ABC_LIBRARY "${STP_DEP_DIR}/lib/${ABC_ARCHIVE}")
endif()

set(ABC_FOUND TRUE)

# SYSTEM: ABC's headers carry warnings STP does not control -- zero-size arrays
# under -Wpedantic, unused parameters in inline helpers -- and a WERROR build
# compiles them as part of every STP translation unit that includes them.
add_library(ABC UNKNOWN IMPORTED GLOBAL)
set_target_properties(ABC PROPERTIES
    IMPORTED_LOCATION "${ABC_LIBRARY}"
    INTERFACE_INCLUDE_DIRECTORIES "${ABC_INCLUDE_DIR}"
    INTERFACE_SYSTEM_INCLUDE_DIRECTORIES "${ABC_INCLUDE_DIR}"
)

mark_as_advanced(ABC_FOUND)
mark_as_advanced(ABC_FOUND_SYSTEM)
mark_as_advanced(ABC_INCLUDE_DIR)
mark_as_advanced(ABC_LIBRARY)

if(ABC_FOUND_SYSTEM)
    message(STATUS "Found ABC: ${ABC_LIBRARY}")
else()
    message(STATUS "Building ABC ${ABC_GIT_TAG}: ${ABC_LIBRARY}")
    add_dependencies(ABC ABC-EP)
endif()

# EOF
