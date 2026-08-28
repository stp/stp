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
# Unlike the other dependencies here, CryptoMiniSat reaches STP entirely
# through the CMake package it installs: cryptominisat5Config.cmake is what
# supplies CRYPTOMINISAT5_LIBRARIES, its static counterpart and that one's
# dependency list, and the include directories. So this module is the ladder in
# cmake/deps-helper.cmake with its third rung missing -- rung 0
# (cryptominisat5_DIR), rung 1 (installed), and then a failure that says what
# to do. STP does not build this one for you, and the message says so.
#
# Which also makes it the one dependency STP_DEPS_LOCAL_ONLY can turn off
# rather than relocate: with rung 1 skipped and no rung 3 behind it, only
# cryptominisat5_DIR is left.
#
# The reasons, because "we did not get round to it" is not one of them:
#
#   - An ExternalProject installs at *build* time, so the config package it
#     would write does not exist during the configure that needs to read it.
#     Every other dependency here is a header and an archive, which a Find
#     module can name for itself; this one is a package whose contents are
#     decided by the package.
#   - Installing it by hand instead -- as MiniSat is, which publishes no
#     config package -- would leave a CryptoMiniSat that a later build could
#     not find by the same means, and would make STP's own
#     STPConfig.cmake name a cryptominisat5 package that did not exist.
#   - CryptoMiniSat >= 5.14 also fetches and installs its own CaDiCaL, which
#     collides with STP's when both are static (see the guard in the top-level
#     CMakeLists), so a build of it is not self-contained the way the others
#     are.
#
# It is also the dependency this matters least for: it is packaged by
# distributions, which is where rung 1 finds it, and scripts/deps/setup-cms.sh
# builds one into deps/install with the flags STP wants.

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
    set(CryptoMiniSat_FOUND FALSE)
    # Deliberately not check_auto_download(): --auto-download cannot help here,
    # so offering it would be a false lead.
    if(CryptoMiniSat_FIND_REQUIRED)
        if(cryptominisat5_FOUND)
            message(FATAL_ERROR
                "Found CryptoMiniSat ${CryptoMiniSat_VERSION}, but STP needs "
                "at least ${CryptoMiniSat_FIND_VERSION}. Every method STP "
                "calls on it exists from that release; older ones are not "
                "refused for being known broken, they are refused for being "
                "untested here -- nothing in this repository builds one.\n"
                "Run scripts/deps/setup-cms.sh, which builds a pinned release "
                "into deps/install where this looks with no further flags, or "
                "build without it: -DUSE_CRYPTOMINISAT=OFF.")
        endif()
        if(STP_DEPS_LOCAL_ONLY)
            message(FATAL_ERROR
                "CryptoMiniSat was not looked for: -DSTP_DEPS_LOCAL_ONLY=ON "
                "confines this build to dependencies inside the build "
                "directory, and CryptoMiniSat is the one dependency STP does "
                "not build for you -- it reaches STP through the CMake "
                "package it installs, which an ExternalProject could not "
                "write until after this configure had needed to read it.\n"
                "Point -Dcryptominisat5_DIR at the directory holding "
                "cryptominisat5Config.cmake, which is rung 0 and is still "
                "honoured, or build without it: -DUSE_CRYPTOMINISAT=OFF.")
        endif()
        message(FATAL_ERROR
            "CryptoMiniSat was not found, and it is the one dependency STP "
            "does not build for you -- it reaches STP through the CMake "
            "package it installs, which an ExternalProject could not write "
            "until after this configure had needed to read it.\n"
            "Install it from your distribution, or run "
            "scripts/deps/setup-cms.sh, which builds one into deps/install "
            "where this looks with no further flags. If it is installed "
            "somewhere unusual, point -Dcryptominisat5_DIR at the directory "
            "holding cryptominisat5Config.cmake. To build without it, "
            "configure with -DUSE_CRYPTOMINISAT=OFF.")
    endif()
    return()
endif()

set(CryptoMiniSat_FOUND TRUE)

message(STATUS "CryptoMiniSat5 dynamic lib: ${CRYPTOMINISAT5_LIBRARIES}")
message(STATUS "CryptoMiniSat5 static lib:  ${CRYPTOMINISAT5_STATIC_LIBRARIES}")
message(STATUS "CryptoMiniSat5 static lib deps: ${CRYPTOMINISAT5_STATIC_LIBRARIES_DEPS}")
message(STATUS "CryptoMiniSat5 include dirs: ${CRYPTOMINISAT5_INCLUDE_DIRS}")
message(STATUS "Found CryptoMiniSat ${CryptoMiniSat_VERSION}: ${CRYPTOMINISAT5_LIBRARIES}")

mark_as_advanced(CryptoMiniSat_FOUND)
mark_as_advanced(CryptoMiniSat_FOUND_SYSTEM)

# EOF
