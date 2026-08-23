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

# Find Riss, the optional -DUSE_RISS backend.
#
#   Riss             imported target, carrying the headers and the archive
#   RISS_INCLUDE_DIR / RISS_LIBRARY
#
# RISS_DIR names a Riss checkout -- the directory holding riss/core/Solver.h,
# with the archive under build/lib -- and is rung 0 of the ladder in
# cmake/deps-helper.cmake.

include(deps-helper)

set(RISS_DIR "" CACHE PATH
    "Path to a Riss checkout: the directory containing riss/core/Solver.h, with build/lib/libriss-coprocessor.a beneath it")

set(Riss_FOUND_SYSTEM FALSE)

if(RISS_DIR)
    # Rung 0. PATHS with NO_DEFAULT_PATH rather than HINTS: find_library
    # reaches CMAKE_PREFIX_PATH before HINTS, and both STP_DEP_DIR and
    # deps/install are on it, so a HINTS lookup could answer with a Riss other
    # than the checkout named here.
    find_path(RISS_INCLUDE_DIR NAMES riss/core/Solver.h
              PATHS ${RISS_DIR} NO_DEFAULT_PATH)
    find_library(RISS_LIBRARY NAMES riss-coprocessor
                 PATHS ${RISS_DIR}/build/lib ${RISS_DIR}/lib NO_DEFAULT_PATH)
    if(NOT RISS_INCLUDE_DIR OR NOT RISS_LIBRARY)
        message(FATAL_ERROR
            "RISS_DIR is '${RISS_DIR}', but no Riss was found there. It should "
            "be a checkout containing riss/core/Solver.h with "
            "build/lib/libriss-coprocessor.a beneath it.")
    endif()
    set(Riss_FOUND_SYSTEM TRUE)
else()
    # Rung 1. Riss is not something a distribution packages, so in practice
    # this finds a copy that another build directory installed into
    # STP_DEP_DIR.
    find_path(RISS_INCLUDE_DIR NAMES riss/core/Solver.h)
    find_library(RISS_LIBRARY NAMES riss-coprocessor)
    if(RISS_INCLUDE_DIR AND RISS_LIBRARY)
        set(Riss_FOUND_SYSTEM TRUE)
    endif()
endif()

if(NOT Riss_FOUND_SYSTEM)
    # Rungs 2 and 3.
    check_ep_downloaded("Riss-EP")
    if(NOT Riss-EP_DOWNLOADED)
        check_auto_download("Riss" "-DUSE_RISS=OFF")
    endif()

    set(Riss_VERSION "41342f15a8e22c78ea7021e85cf4a98e79eb349c" CACHE STRING
        "Riss revision to build when one has to be built")
    mark_as_advanced(Riss_VERSION)

    set(Riss_ARCHIVE
        "${CMAKE_STATIC_LIBRARY_PREFIX}riss-coprocessor${CMAKE_STATIC_LIBRARY_SUFFIX}")

    # Riss needs flags of its own, so its CMAKE_CXX_FLAGS is given last and
    # wins over the one in STP_EP_COMMON_CMAKE_ARGS. STP's flags are still
    # carried in front of Riss's, so a sanitizer build reaches it:
    #
    #   -std=gnu++14    Riss does not build as C++17. Only its own translation
    #                   units need this -- the headers STP includes are
    #                   C++17-clean.
    #
    # The warning silencing every dependency gets comes from
    # STP_EP_NO_WARNINGS; this only has to add what is particular to Riss.
    set(Riss_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${STP_EP_NO_WARNINGS} -std=gnu++14")

    ExternalProject_Add(
        Riss-EP
        ${STP_EP_COMMON_CONFIG}
        GIT_REPOSITORY https://github.com/conp-solutions/riss
        GIT_TAG ${Riss_VERSION}
        CMAKE_ARGS ${STP_EP_COMMON_CMAKE_ARGS}
                   -DCMAKE_INSTALL_PREFIX=<INSTALL_DIR>
                   # Riss predates the minimum CMake 4 will accept, by more
                   # than the 3.12 the common arguments ask for.
                   -DCMAKE_POLICY_VERSION_MINIMUM=3.5
                   "-DCMAKE_CXX_FLAGS=${Riss_CXX_FLAGS}"
        # STP links the coprocessor library and nothing else; Riss's default
        # target list also builds several solvers and their tools.
        BUILD_COMMAND ${CMAKE_COMMAND} --build . --config ${CMAKE_BUILD_TYPE}
                      --target riss-coprocessor-lib-static
        # Riss has no install rules at all, which is why RISS_DIR names a
        # checkout rather than a prefix.
        INSTALL_COMMAND ${CMAKE_COMMAND}
                        -DSRC=<SOURCE_DIR> -DBIN=<BINARY_DIR>
                        -DDST=<INSTALL_DIR> -DLIBNAME=${Riss_ARCHIVE}
                        -P "${CMAKE_CURRENT_LIST_DIR}/deps-utils/riss-install.cmake"
        BUILD_BYPRODUCTS <INSTALL_DIR>/lib/${Riss_ARCHIVE}
    )
    add_dependencies(deps Riss-EP)

    set(RISS_INCLUDE_DIR "${STP_DEP_DIR}/include")
    set(RISS_LIBRARY "${STP_DEP_DIR}/lib/${Riss_ARCHIVE}")
endif()

set(Riss_FOUND TRUE)

# SYSTEM: Riss is upstream code whose warnings STP does not control, and it is
# consumed as headers rather than as a target STP builds, so there is no target
# to hang a -Wno-error on. Without it a WERROR build fails inside Riss's own
# headers, some ninety diagnostics across a dozen files.
add_library(Riss UNKNOWN IMPORTED GLOBAL)
set_target_properties(Riss PROPERTIES
    IMPORTED_LOCATION "${RISS_LIBRARY}"
    INTERFACE_INCLUDE_DIRECTORIES "${RISS_INCLUDE_DIR}"
    INTERFACE_SYSTEM_INCLUDE_DIRECTORIES "${RISS_INCLUDE_DIR}"
)

mark_as_advanced(Riss_FOUND)
mark_as_advanced(Riss_FOUND_SYSTEM)
mark_as_advanced(RISS_INCLUDE_DIR)
mark_as_advanced(RISS_LIBRARY)

if(Riss_FOUND_SYSTEM)
    message(STATUS "Found Riss: ${RISS_LIBRARY}")
else()
    message(STATUS "Building Riss ${Riss_VERSION}: ${RISS_LIBRARY}")
    add_dependencies(Riss Riss-EP)
endif()

# EOF
