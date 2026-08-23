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
# STP's warning set and -Werror are about STP's code. Forwarded into a
# dependency's build they make it fail on warnings nobody here can fix, which
# is why every dependency STP used to compile in-tree was handed -Wno-error
# one at a time. A separate build needs the same and gets it here, once: STP
# does not police upstream code's warnings, and an ExternalProject's output is
# logged to a file rather than the console anyway, so silencing beats
# demoting.
if(MSVC)
    set(STP_EP_NO_WARNINGS "/w")
else()
    set(STP_EP_NO_WARNINGS "-w")
endif()

set(STP_EP_COMMON_CMAKE_ARGS
    -DCMAKE_BUILD_TYPE=${CMAKE_BUILD_TYPE}
    -DCMAKE_C_COMPILER=${CMAKE_C_COMPILER}
    -DCMAKE_CXX_COMPILER=${CMAKE_CXX_COMPILER}
    "-DCMAKE_C_FLAGS=${CMAKE_C_FLAGS} ${STP_EP_NO_WARNINGS}"
    "-DCMAKE_CXX_FLAGS=${CMAKE_CXX_FLAGS} ${STP_EP_NO_WARNINGS}"
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

# MSVC writes debug information to a shared program database by default, and
# two source files compiling in parallel then race for it -- "cannot open
# program database", which is what a Windows job gets. STP's own MSVC build
# already avoids this by asking for embedded debug info; a dependency built
# separately does not inherit that, so say it again here. CMP0141 is what makes
# the variable mean anything.
if(MSVC)
    set(_stp_ep_msvc_debug "${CMAKE_MSVC_DEBUG_INFORMATION_FORMAT}")
    if(NOT _stp_ep_msvc_debug)
        set(_stp_ep_msvc_debug "Embedded")
    endif()
    list(APPEND STP_EP_COMMON_CMAKE_ARGS
         -DCMAKE_POLICY_DEFAULT_CMP0141=NEW
         "-DCMAKE_MSVC_DEBUG_INFORMATION_FORMAT=${_stp_ep_msvc_debug}")
    unset(_stp_ep_msvc_debug)

    # Same shape of problem, one step further along: which C runtime everyone
    # links. A static STP switches itself to /MT -- by rewriting its own
    # per-configuration flags, and by add_compile_options(/MT), neither of
    # which a separately configured sub-build can see. The dependency keeps
    # CMake's default /MD, and the two archives cannot be linked together:
    #
    #   error LNK2038: mismatch detected for 'RuntimeLibrary': value
    #   'MD_DynamicRelease' doesn't match value 'MT_StaticRelease'
    #
    # with a run of LNK2005 duplicate-symbol errors against msvcprt.lib and
    # unresolved __imp_-prefixed CRT symbols behind it, all one cause.
    #
    # CMAKE_MSVC_RUNTIME_LIBRARY is the abstraction for this, and CMP0141's
    # neighbour CMP0091 is what makes it mean anything -- without the policy,
    # the choice stays welded into the default flags where we cannot reach it.
    # An explicit setting from the user wins; otherwise follow the same rule
    # STP applies to itself, keyed on BUILD_SHARED_LIBS, which STATICCOMPILE
    # has already turned off by the time this file is included.
    if(CMAKE_MSVC_RUNTIME_LIBRARY)
        set(_stp_ep_msvc_runtime "${CMAKE_MSVC_RUNTIME_LIBRARY}")
    else()
        # A multi-config generator has no CMAKE_BUILD_TYPE to read, so leave
        # the configuration to a generator expression there and settle it here
        # everywhere else.
        if(CMAKE_BUILD_TYPE)
            if(CMAKE_BUILD_TYPE MATCHES "^[Dd][Ee][Bb][Uu][Gg]$")
                set(_stp_ep_msvc_runtime "MultiThreadedDebug")
            else()
                set(_stp_ep_msvc_runtime "MultiThreaded")
            endif()
        else()
            set(_stp_ep_msvc_runtime "MultiThreaded$<$<CONFIG:Debug>:Debug>")
        endif()
        if(BUILD_SHARED_LIBS)
            string(APPEND _stp_ep_msvc_runtime "DLL")
        endif()
    endif()
    list(APPEND STP_EP_COMMON_CMAKE_ARGS
         -DCMAKE_POLICY_DEFAULT_CMP0091=NEW
         "-DCMAKE_MSVC_RUNTIME_LIBRARY=${_stp_ep_msvc_runtime}")
    message(STATUS "Dependency MSVC runtime: ${_stp_ep_msvc_runtime}")
    unset(_stp_ep_msvc_runtime)
endif()

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
    # ABC's defines are in here and the build type is not, which looks
    # inconsistent and is not. Sharing an ABC compiled at a different
    # optimisation level is merely a choice; sharing one compiled with a
    # different ABC_PTRUINT_T width than STP's own translation units assume is
    # a crash in CNF generation.
    set(_now
        "compiler=${CMAKE_CXX_COMPILER_ID} ${CMAKE_CXX_COMPILER_VERSION}\n"
        "sanitize=${SANITIZE}\n"
        "toolchain=${CMAKE_TOOLCHAIN_FILE}\n"
        "abc_abi=${ABC_ABI_DEFINITIONS}\n")
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
