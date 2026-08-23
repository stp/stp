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

# Shared machinery for the cmake/FindX.cmake modules that can build a
# dependency when the system has not got one.
#
# Each of those modules works down the same ladder:
#
#   0. <X>_DIR names a copy explicitly -- use it, or fail. Never fall through:
#      silently building a different copy than the one the caller named is a
#      worse outcome than stopping.
#   1. the system, which includes anything on CMAKE_PREFIX_PATH -- so a
#      dependency already installed into ${STP_DEP_DIR}, or into the
#      deps/install that scripts/deps/*.sh used to write, is found here.
#   2. an ExternalProject this build directory already downloaded.
#   3. ENABLE_AUTO_DOWNLOAD -- fetch and build it.
#   4. fail, naming both --auto-download and -D<X>_DIR=.
#
# Rung 1 is what makes a shared dependency directory work: the second build
# directory pointed at one finds the artefacts there and never creates an
# ExternalProject at all.

include_guard(GLOBAL)

include(ExternalProject)

option(ENABLE_AUTO_DOWNLOAD
       "Download and build missing dependencies instead of failing" OFF)
add_feature_info(AutoDownload ENABLE_AUTO_DOWNLOAD
                 "Downloads and builds dependencies that are not installed")

# -----------------------------------------------------------------------------
# Where dependencies are built, and where they are installed
# -----------------------------------------------------------------------------
# These are deliberately two different things.
#
# The scratch tree -- ExternalProject's src/, tmp/ and stamp/ -- is
# per-build-directory and not negotiable. Stamp files are mutable
# per-configuration state, and two builds sharing them corrupt each other.
#
# The install tree is write-once and its contents are fully determined by the
# pinned revision, so it can be shared. STP_DEP_DIR names it, and it also goes
# on CMAKE_PREFIX_PATH, which is the whole trick: point several build
# directories at one and only the first pays to build anything, because the
# rest find what it installed at rung 1 of the ladder above and create no
# ExternalProject.
set(STP_DEPS_PREFIX "${PROJECT_BINARY_DIR}/deps")
set(STP_DEP_DIR "${STP_DEPS_PREFIX}/install" CACHE PATH
    "Where built dependencies are installed, and looked for. Point several build directories at one to build them once")

# CMake insists a directory named by INTERFACE_INCLUDE_DIRECTORIES exists when
# the property is set, which is before any ExternalProject has run.
file(MAKE_DIRECTORY "${STP_DEP_DIR}/include")

# Ahead of everything else, so that a dependency this build installed outranks
# a system copy. deps/install -- where scripts/deps/*.sh installs -- is
# appended by the top-level CMakeLists and stays behind it.
list(PREPEND CMAKE_PREFIX_PATH "${STP_DEP_DIR}")

# Builds every dependency that this configure decided to build, and nothing
# else, so that a shared STP_DEP_DIR can be warmed once before several build
# directories are pointed at it:
#
#   cmake -S . -B warm -DSTP_DEP_DIR=... -DENABLE_AUTO_DOWNLOAD=ON ...
#   cmake --build warm --target deps
#
# Declared unconditionally, including when every dependency was found and no
# ExternalProject exists, so that a script calling it does not break the moment
# the directory is warm.
if(NOT TARGET deps)
    add_custom_target(deps)
endif()

# -----------------------------------------------------------------------------
# What a dependency is built with
# -----------------------------------------------------------------------------
# STP's toolchain, forwarded. Without this a dependency is built by whatever
# `cc` happens to be first on PATH, at whatever optimisation its own defaults
# pick -- which is what the scripts/deps/*.sh scripts did, and why none of them
# survived a cross-compile, a sanitizer build or a compiler launcher.
#
# Individual modules append to this, and a later -D wins, so a dependency that
# needs something different (Riss does not compile as C++17, MiniSat predates
# CMake 4's floor) can still say so.
#
# POSITION_INDEPENDENT_CODE unconditionally: every static dependency STP has is
# linked into libstp.so, and each of the scripts this replaces had to remember
# that separately.
set(STP_EP_COMMON_CMAKE_ARGS
    -DCMAKE_BUILD_TYPE=${CMAKE_BUILD_TYPE}
    -DCMAKE_C_COMPILER=${CMAKE_C_COMPILER}
    -DCMAKE_CXX_COMPILER=${CMAKE_CXX_COMPILER}
    -DCMAKE_C_FLAGS=${CMAKE_C_FLAGS}
    -DCMAKE_CXX_FLAGS=${CMAKE_CXX_FLAGS}
    -DCMAKE_C_COMPILER_LAUNCHER=${CMAKE_C_COMPILER_LAUNCHER}
    -DCMAKE_CXX_COMPILER_LAUNCHER=${CMAKE_CXX_COMPILER_LAUNCHER}
    -DCMAKE_POSITION_INDEPENDENT_CODE=ON
    -DCMAKE_TOOLCHAIN_FILE=${CMAKE_TOOLCHAIN_FILE}
    -DCMAKE_OSX_SYSROOT=${CMAKE_OSX_SYSROOT}
    -DCMAKE_OSX_ARCHITECTURES=${CMAKE_OSX_ARCHITECTURES}
    # Do not let a dependency register itself in the user's CMake package
    # registry, where it would then be found by unrelated projects.
    -DCMAKE_EXPORT_NO_PACKAGE_REGISTRY=ON
    # Several of these projects predate the minimum CMake 4 accepts.
    -DCMAKE_POLICY_VERSION_MINIMUM=3.12
)

set(STP_EP_COMMON_CONFIG
    PREFIX "${STP_DEPS_PREFIX}"
    INSTALL_DIR "${STP_DEP_DIR}"
    # Quiet by default, because a dependency's build is not what anyone
    # configuring STP is trying to read -- but printed in full if it fails,
    # which is the property the shell scripts had for free and an
    # ExternalProject does not.
    LOG_DOWNLOAD ON
    LOG_UPDATE ON
    LOG_PATCH ON
    LOG_CONFIGURE ON
    LOG_BUILD ON
    LOG_INSTALL ON
    LOG_MERGED_STDOUTERR ON
    LOG_OUTPUT_ON_FAILURE ON
)

# -----------------------------------------------------------------------------
# Is the shared directory the right shape for this build?
# -----------------------------------------------------------------------------
# A shared STP_DEP_DIR holds one libbf.a, whatever compiled it. Point an ASan
# build and a plain build at the same one and they overwrite each other's, and
# the result is a link error or a sanitizer runtime mismatch that says nothing
# about where it came from.
#
# So record what produced the contents and say so when the next build
# disagrees. A warning rather than an error: sharing is the point of the
# variable, and a rebuild into a separate directory is the caller's call.
#
# Only the fields that can actually break a link are recorded. The build type
# deliberately is not: several build types sharing one dependency directory is
# the ordinary use, and warning about it would make the warning worthless.
function(stp_check_dep_dir_config)
    set(_now
        "compiler=${CMAKE_CXX_COMPILER_ID} ${CMAKE_CXX_COMPILER_VERSION}\n"
        "sanitize=${SANITIZE}\n"
        "toolchain=${CMAKE_TOOLCHAIN_FILE}\n")
    string(JOIN "" _now ${_now})

    set(_stamp "${STP_DEP_DIR}/.stp-dep-config")
    if(EXISTS "${_stamp}")
        file(READ "${_stamp}" _was)
        if(NOT _was STREQUAL _now)
            message(WARNING
                "The dependency directory\n    ${STP_DEP_DIR}\n"
                "was filled by a different configuration than this one.\n\n"
                "  it holds:  ${_was}"
                "  this is:   ${_now}\n"
                "Its libraries will be linked into this build as they are. If "
                "that is not what you want, give this build a dependency "
                "directory of its own with -DSTP_DEP_DIR=<path>.")
        endif()
    endif()
    file(WRITE "${_stamp}" "${_now}")
endfunction()

# -----------------------------------------------------------------------------
# The rungs
# -----------------------------------------------------------------------------

# Rung 3: refuse to download unless we were told we may, and say how to allow it
# or to avoid needing it. `disable_option` is what turns this dependency off, or
# "" for one that is not optional. An optional third argument names the variable
# that points at an existing copy, for a dependency whose variable is not simply
# the uppercased name -- cryptominisat5_DIR, spelled by its upstream package,
# rather than LIBBF_DIR, CADICAL_DIR and RISS_DIR.
macro(check_auto_download name disable_option)
    if(NOT ENABLE_AUTO_DOWNLOAD)
        if(${ARGC} GREATER 2)
            set(_dirvar "${ARGV2}")
        else()
            string(TOUPPER "${name}" _dirvar)
            set(_dirvar "${_dirvar}_DIR")
        endif()
        if(${name}_FIND_VERSION)
            set(_depname "${name} (>= ${${name}_FIND_VERSION})")
        else()
            set(_depname "${name}")
        endif()
        if("${disable_option}" STREQUAL "")
            message(FATAL_ERROR
                "Could not find ${_depname}, which STP requires. Install it, "
                "point -D${_dirvar} at a copy, or configure with "
                "-DENABLE_AUTO_DOWNLOAD=ON to have it downloaded and built "
                "here.")
        else()
            message(FATAL_ERROR
                "Could not find ${_depname}. Install it, point -D${_dirvar} "
                "at a copy, configure with -DENABLE_AUTO_DOWNLOAD=ON to have "
                "it downloaded and built here, or leave it out with "
                "${disable_option}.")
        endif()
    endif()
endmacro()

# Rung 2: this build directory already downloaded it on an earlier configure,
# so do not ask for --auto-download a second time.
macro(check_ep_downloaded name)
    if(EXISTS "${STP_DEPS_PREFIX}/src/${name}")
        set(${name}_DOWNLOADED TRUE)
    else()
        set(${name}_DOWNLOADED FALSE)
    endif()
endmacro()

# Clear ${name}_FOUND_SYSTEM when the copy that was found is too old or too new
# for what find_package(${name} <version>) asked for.
macro(check_system_version name)
    if(${name}_FIND_VERSION AND ${name}_VERSION)
        if(${name}_VERSION VERSION_LESS ${name}_FIND_VERSION)
            message(STATUS "System ${name} is ${${name}_VERSION}, but at least "
                           "${${name}_FIND_VERSION} is required")
            set(${name}_FOUND_SYSTEM FALSE)
        endif()
    endif()
    if(${name}_FIND_VERSION_MAX AND ${name}_VERSION)
        if(${name}_VERSION VERSION_GREATER ${name}_FIND_VERSION_MAX)
            message(STATUS "System ${name} is ${${name}_VERSION}, but at most "
                           "${${name}_FIND_VERSION_MAX} is supported")
            set(${name}_FOUND_SYSTEM FALSE)
        endif()
    endif()
endmacro()

# EOF
