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

# Find CryptoMiniSat, the -DUSE_CRYPTOMINISAT backend.
#
# The full ladder from cmake/deps-helper.cmake: rung 0 (cryptominisat5_DIR),
# rung 1 (installed, which distributions provide), rungs 2 and 3 (built here).
#
# The first two rungs go through the CMake package CryptoMiniSat installs:
# cryptominisat5Config.cmake supplies CRYPTOMINISAT5_LIBRARIES, its static
# counterpart and that one's dependency list, and the include directories.
# Rung 3 cannot, and that is why this module had no rung 3 for as long as it
# did -- an ExternalProject installs at *build* time, so the package it writes
# does not exist during the configure that has to read it. Every other
# dependency here is a header and an archive that a Find module names for
# itself; this one was a package whose contents the package decided.
#
# What changed is what gets built. stp/cryptominisat's `stp` branch carries a
# NOCADICAL option, and with it CryptoMiniSat stops fetching, building and
# installing a CaDiCaL of its own -- which was both a collision with STP's (see
# the guard in the top-level CMakeLists) and the reason its link interface
# named an imported target a consumer had to resolve. What is left is an
# archive whose link interface is Threads and GMP: a header and an archive,
# nameable here exactly as cmake/FindCaDiCaL.cmake names CaDiCaL's.
#
# So rung 3 does not read the package at all, and STPConfig.cmake.in asks a
# consumer to find_dependency(cryptominisat5) only when rung 0 or 1 supplied
# one -- STP_CMS_FROM_PACKAGE, set at the end of this file.
#
# The option is sound for STP because backbone extraction is the only thing
# CryptoMiniSat wants CaDiCaL for, reached only through its "backbone"
# simplification token or backbone_simpl(), and STP calls neither.
#
# One way this module still differs: CryptoMiniSat is optional.
# USE_CRYPTOMINISAT defaults to AUTO, so not finding one is not the error that
# a missing ABC is -- see the note at rung 2.

include(deps-helper)

set(cryptominisat5_DIR "" CACHE PATH
    "Path to the directory containing cryptominisat5Config.cmake")

# Rungs 0 and 1 are one call here, so STP_DEPS_LOCAL_ONLY cannot skip the
# second by itself: it skips the whole search unless cryptominisat5_DIR names a
# copy, which is rung 0 and stays honoured. With no rung 3 to fall back on that
# leaves nothing, which is the honest answer -- STP does not build this one, so
# under that option a named copy is the only way to have it at all.
if(cryptominisat5_DIR OR NOT STP_DEPS_LOCAL_ONLY)
    # STP does not look for GMP. It is CryptoMiniSat's dependency, not STP's:
    # no STP source includes it, and it reaches STP through the cryptominisat5
    # imported target, whose link interface names PkgConfig::GMP (its header
    # includes gmpxx.h, so the include path travels the same way; see
    # lib/Sat/CMakeLists.txt). cryptominisat5Config.cmake asks pkg-config for
    # gmp with REQUIRED, which is a FATAL_ERROR raised from inside that file
    # when CryptoMiniSat is installed but its gmp.pc is not, and nothing STP
    # does can turn it into "not found". So say what is about to be asked, and
    # of whom, before asking: nothing can be printed after the abort, and the
    # error itself names gmp but not the fix.
    message(STATUS "Looking for CryptoMiniSat5 (its CMake package needs GMP via "
                   "pkg-config; if this fails on 'gmp', install libgmp-dev or "
                   "configure with -DUSE_CRYPTOMINISAT=OFF)")

    # A static CryptoMiniSat references cadical/cadiback imported targets but
    # its config file does not find them itself; a shared CryptoMiniSat has no
    # such packages, hence QUIET. cadical's export in turn references
    # Threads::Threads.
    find_package(Threads QUIET)
    find_package(cadical CONFIG QUIET)
    find_package(cadiback CONFIG QUIET)

    # find_package(CONFIG) honours cryptominisat5_DIR first and
    # CMAKE_PREFIX_PATH -- which carries STP_DEP_DIR and deps/install -- after
    # it.
    #
    # Deliberately not asking find_package for the version: it is checked here
    # instead, so that a copy which is present but too old can be reported as
    # exactly that. "Could not find CryptoMiniSat" is a confusing thing to be
    # told about a library that is plainly installed.
    find_package(cryptominisat5 CONFIG)
endif()

set(CryptoMiniSat_FOUND_SYSTEM FALSE)
if(cryptominisat5_FOUND)
    set(CryptoMiniSat_FOUND_SYSTEM TRUE)
    set(CryptoMiniSat_VERSION "${cryptominisat5_VERSION}")
    # Clears CryptoMiniSat_FOUND_SYSTEM if it is outside the range STP asked
    # for, and says so.
    check_system_version("CryptoMiniSat")
endif()

if(NOT CryptoMiniSat_FOUND_SYSTEM)
    # Rungs 2 and 3, which this module did without for as long as a build of
    # CryptoMiniSat was not self-contained. What it reached STP as was a CMake
    # package -- one an ExternalProject writes at build time, too late for the
    # configure that has to read it. That is still true of the package, and the
    # way past it is to stop needing one: what stp/cryptominisat's `stp` branch
    # builds is an archive and a header, the shape every other dependency here
    # arrives in, so this can name the pieces itself exactly as
    # cmake/FindCaDiCaL.cmake does.
    #
    # The branch is what makes that possible. Upstream CryptoMiniSat >= 5.14
    # fetches and installs its own CaDiCaL, whose imported target a static
    # libcryptominisat5 then names in its link interface -- so a consumer that
    # did not go through the package would be left with an unresolved `cadical`
    # target, and one that did would put a second CaDiCaL on libstp's link
    # line. Built -DNOCADICAL=ON the link interface is Threads and GMP and
    # nothing else, which is nameable here. The option is sound for STP because
    # nothing in STP asks for backbone extraction, which is all CryptoMiniSat
    # wants CaDiCaL for.
    #
    # Unlike the others on this ladder, CryptoMiniSat is optional:
    # USE_CRYPTOMINISAT defaults to AUTO, which means "use it if it is there".
    # So a missing one may not become an error the way a missing ABC does --
    # check_auto_download() is fatal by construction, and is reached only when
    # this was asked for by name. Otherwise the answer is the one AUTO asks
    # for: say nothing and build without it.
    check_ep_downloaded("CryptoMiniSat-EP")
    if(NOT CryptoMiniSat-EP_DOWNLOADED AND NOT ENABLE_AUTO_DOWNLOAD)
        if(CryptoMiniSat_FIND_REQUIRED)
            check_auto_download("CryptoMiniSat" "-DUSE_CRYPTOMINISAT=OFF"
                                "cryptominisat5_DIR")
        endif()
        set(CryptoMiniSat_FOUND FALSE)
        set(STP_CMS_FROM_PACKAGE FALSE)
        return()
    endif()

    # Pinned to a commit, as MiniSat, LibBF, SymFPU and ABC are. It is the head
    # of the `stp` branch: release/v5.14.7 plus the NOCADICAL option.
    set(CryptoMiniSat_COMMIT "261392c4e993f40638392012b689a0a4a7794355"
        CACHE STRING "CryptoMiniSat commit to build when one has to be built")
    mark_as_advanced(CryptoMiniSat_COMMIT)
    # Not read off the checkout: nothing is checked out yet at configure time,
    # and the commit above fixes which release this is.
    set(CryptoMiniSat_VERSION "5.14.7")

    set(CryptoMiniSat_ARCHIVE
        "${CMAKE_STATIC_LIBRARY_PREFIX}cryptominisat5${CMAKE_STATIC_LIBRARY_SUFFIX}")

    # STATIC_BINARY=OFF: that switch is for CryptoMiniSat's own command-line
    # solver, and wants a static gmp and zlib that STP does not need.
    ExternalProject_Add(
        CryptoMiniSat-EP
        ${STP_EP_COMMON_CONFIG}
        GIT_REPOSITORY https://github.com/stp/cryptominisat
        GIT_TAG ${CryptoMiniSat_COMMIT}
        CMAKE_ARGS ${STP_EP_COMMON_CMAKE_ARGS}
                   -DCMAKE_INSTALL_PREFIX=<INSTALL_DIR>
                   -DCMAKE_INSTALL_LIBDIR=lib
                   -DNOCADICAL=ON
                   -DBUILD_SHARED_LIBS=OFF
                   -DSTATIC_BINARY=OFF
                   -DENABLE_ASSERTIONS=OFF
                   -DENABLE_TESTING=OFF
        BUILD_BYPRODUCTS <INSTALL_DIR>/lib/${CryptoMiniSat_ARCHIVE}
    )
    add_dependencies(deps CryptoMiniSat-EP)

    # GMP is CryptoMiniSat's dependency and STP has never had to look for it:
    # cryptominisat5Config.cmake did, and the target it wrote carried
    # PkgConfig::GMP into STP's link and its include directory into the compile
    # of CryptoMinisat5.cpp, which includes gmpxx.h through cryptominisat.h.
    # Without that package this is the one thing that has to be picked up here
    # instead -- the same lookup, in the same shape, moved one level out.
    find_package(PkgConfig REQUIRED)
    pkg_check_modules(GMP REQUIRED IMPORTED_TARGET gmp)
    find_package(Threads REQUIRED)
    # gmpxx is a separate archive from gmp and pkg-config does not name it;
    # CryptoMiniSat's own config finds it the same way and puts it first.
    find_library(GMPXX_LIBRARY NAMES gmpxx HINTS ${GMP_LIBRARY_DIRS})
    set(_cms_link "Threads::Threads")
    if(GMPXX_LIBRARY)
        list(APPEND _cms_link "${GMPXX_LIBRARY}")
    endif()
    list(APPEND _cms_link "PkgConfig::GMP")

    # Deliberately no INTERFACE_INCLUDE_DIRECTORIES, so that this target
    # behaves as the packaged one does: it carries the link interface and not
    # CryptoMiniSat's own header directory, which CRYPTOMINISAT5_INCLUDE_DIRS
    # carries instead and lib/Sat/CMakeLists.txt gives to the single source
    # file that includes cryptominisat.h. See the note there for why that is
    # not tidiness.
    add_library(cryptominisat5 UNKNOWN IMPORTED GLOBAL)
    set_target_properties(cryptominisat5 PROPERTIES
        IMPORTED_LOCATION "${STP_DEP_DIR}/lib/${CryptoMiniSat_ARCHIVE}"
        INTERFACE_LINK_LIBRARIES "${_cms_link}"
    )
    unset(_cms_link)
    # The ordering edge. add_dependencies(deps ...) only warms a shared
    # STP_DEP_DIR on request; without this, libstp links against an archive the
    # ExternalProject has not installed yet, which is a race that surfaces as
    # "cannot find .../libcryptominisat5.a" from ld and not from CMake.
    add_dependencies(cryptominisat5 CryptoMiniSat-EP)

    # The names the rest of the tree reads, spelled as the package spells them.
    set(CRYPTOMINISAT5_LIBRARIES cryptominisat5)
    set(CRYPTOMINISAT5_STATIC_LIBRARIES cryptominisat5)
    set(CRYPTOMINISAT5_STATIC_LIBRARIES_DEPS "")
    set(CRYPTOMINISAT5_INCLUDE_DIRS "${STP_DEP_DIR}/include")
endif()

# Whether CryptoMiniSat arrived as a CMake package. STPConfig.cmake.in asks a
# consumer to find_dependency(cryptominisat5) only then: what rung 3 leaves is
# an archive named by path in STP's own exported targets, the way every other
# dependency built here is carried, and no package for a consumer to find.
set(STP_CMS_FROM_PACKAGE ${CryptoMiniSat_FOUND_SYSTEM})

set(CryptoMiniSat_FOUND TRUE)

message(STATUS "CryptoMiniSat5 dynamic lib: ${CRYPTOMINISAT5_LIBRARIES}")
message(STATUS "CryptoMiniSat5 static lib:  ${CRYPTOMINISAT5_STATIC_LIBRARIES}")
message(STATUS "CryptoMiniSat5 static lib deps: ${CRYPTOMINISAT5_STATIC_LIBRARIES_DEPS}")
message(STATUS "CryptoMiniSat5 include dirs: ${CRYPTOMINISAT5_INCLUDE_DIRS}")
message(STATUS "Found CryptoMiniSat ${CryptoMiniSat_VERSION}: ${CRYPTOMINISAT5_LIBRARIES}")

mark_as_advanced(CryptoMiniSat_FOUND)
mark_as_advanced(CryptoMiniSat_FOUND_SYSTEM)

# EOF
