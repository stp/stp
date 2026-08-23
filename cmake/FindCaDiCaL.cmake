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

# Find CaDiCaL, the -DUSE_CADICAL backend.
#
#   CaDiCaL              imported target, carrying the header and the archive
#   CADICAL_VERSION      what was found, or "unknown"
#   CADICAL_HAS_FACTOR   bounded variable addition is available
#   CADICAL_HAS_INPROBING  the "inprobing" option is available
#
# CADICAL_DIR names a CaDiCaL checkout -- the directory holding src/cadical.hpp
# with build/libcadical.a beneath it -- and is rung 0 of the ladder in
# cmake/deps-helper.cmake.

include(deps-helper)

set(CADICAL_DIR "" CACHE PATH
    "Path to a CaDiCaL checkout: the directory containing src/cadical.hpp, with build/libcadical.a beneath it")

set(CaDiCaL_FOUND_SYSTEM FALSE)
set(CADICAL_VERSION "unknown")

# Everything downstream includes <cadical/cadical.hpp>, which is where an
# installed CaDiCaL puts its header. A checkout has it at src/cadical.hpp, so
# rung 0 stages a copy under the installed name and every rung then presents
# the same layout. See the note in include/stp/Sat/Cadical.h.
set(CADICAL_STAGED_INCLUDE_DIR "${PROJECT_BINARY_DIR}/deps/staged-include")

if(CADICAL_DIR)
    # Rung 0. PATHS with NO_DEFAULT_PATH rather than HINTS, so that CADICAL_DIR
    # decides and nothing else gets a say. find_library searches
    # CMAKE_PREFIX_PATH before it reaches HINTS, and both STP_DEP_DIR and
    # deps/install are on it -- and CryptoMiniSat >= 5.14 installs its own
    # bundled CaDiCaL into a prefix like that. STP once compiled against the
    # headers CADICAL_DIR named and linked a different CaDiCaL's library
    # because of exactly this.
    find_path(CADICAL_CHECKOUT_DIR NAMES src/cadical.hpp
              PATHS ${CADICAL_DIR} NO_DEFAULT_PATH)
    find_library(CADICAL_LIBRARY NAMES cadical
                 PATHS ${CADICAL_DIR}/build ${CADICAL_DIR}/lib NO_DEFAULT_PATH)
    if(NOT CADICAL_CHECKOUT_DIR OR NOT CADICAL_LIBRARY)
        message(FATAL_ERROR
            "CADICAL_DIR is '${CADICAL_DIR}', but no CaDiCaL was found there. "
            "It should be a checkout containing src/cadical.hpp with "
            "build/libcadical.a beneath it.")
    endif()
    configure_file("${CADICAL_CHECKOUT_DIR}/src/cadical.hpp"
                   "${CADICAL_STAGED_INCLUDE_DIR}/cadical/cadical.hpp" COPYONLY)
    set(CADICAL_INCLUDE_DIR "${CADICAL_STAGED_INCLUDE_DIR}")
    # A checkout carries its version in a VERSION file at its root.
    if(EXISTS "${CADICAL_CHECKOUT_DIR}/VERSION")
        file(READ "${CADICAL_CHECKOUT_DIR}/VERSION" CADICAL_VERSION)
        string(STRIP "${CADICAL_VERSION}" CADICAL_VERSION)
    endif()
    set(CaDiCaL_FOUND_SYSTEM TRUE)
else()
    # Rung 1. Includes a CaDiCaL that another build directory installed into
    # STP_DEP_DIR.
    find_path(CADICAL_INCLUDE_DIR NAMES cadical/cadical.hpp)
    find_library(CADICAL_LIBRARY NAMES cadical)
    if(CADICAL_INCLUDE_DIR AND CADICAL_LIBRARY)
        set(CaDiCaL_FOUND_SYSTEM TRUE)
        # There is no VERSION file to read here, and the header carries no
        # version macro, so ask the library itself. This is what an installed
        # CaDiCaL used to lose: the probe read a checkout-only path, came back
        # "unknown", and --cadical-factor was silently disabled.
        set(_ver_src "${PROJECT_BINARY_DIR}/CaDiCaL_version.cpp")
        file(WRITE "${_ver_src}"
             "#include <cadical/cadical.hpp>\n"
             "#include <iostream>\n"
             "int main() { std::cout << CaDiCaL::Solver::version() << std::endl; return 0; }\n")
        try_run(_run_result _compile_result
                "${PROJECT_BINARY_DIR}" "${_ver_src}"
                CMAKE_FLAGS "-DINCLUDE_DIRECTORIES=${CADICAL_INCLUDE_DIR}"
                LINK_LIBRARIES ${CADICAL_LIBRARY}
                RUN_OUTPUT_VARIABLE _ver_out)
        if(_compile_result AND _run_result EQUAL 0)
            string(STRIP "${_ver_out}" CADICAL_VERSION)
        endif()
    endif()
endif()

if(NOT CaDiCaL_FOUND_SYSTEM)
    # Rungs 2 and 3.
    check_ep_downloaded("CaDiCaL-EP")
    if(NOT CaDiCaL-EP_DOWNLOADED)
        check_auto_download("CaDiCaL" "-DUSE_CADICAL=OFF")
    endif()

    set(CaDiCaL_TAG "rel-3.0.1" CACHE STRING
        "CaDiCaL tag to build when one has to be built")
    mark_as_advanced(CaDiCaL_TAG)
    # The tag is rel-<version>, and the version is what the feature gates below
    # are decided from -- so derive one from the other rather than writing the
    # number twice and letting them drift.
    string(REGEX REPLACE "^rel-" "" CADICAL_VERSION "${CaDiCaL_TAG}")

    set(CaDiCaL_ARCHIVE
        "${CMAKE_STATIC_LIBRARY_PREFIX}cadical${CMAKE_STATIC_LIBRARY_SUFFIX}")

    # CaDiCaL has no CMake. It has a configure script that writes a makefile
    # into build/, which is what STP's own recipe has always driven, so drive
    # the same one: -fPIC because libcadical.a is linked into libstp.so, and
    # CaDiCaL's configure does not build position-independent code by default.
    #
    # BUILD_IN_SOURCE, because that is where its configure puts build/.
    ExternalProject_Add(
        CaDiCaL-EP
        ${STP_EP_COMMON_CONFIG}
        GIT_REPOSITORY https://github.com/arminbiere/cadical
        GIT_TAG ${CaDiCaL_TAG}
        BUILD_IN_SOURCE ON
        CONFIGURE_COMMAND <SOURCE_DIR>/configure -fPIC
        # Only the library: CaDiCaL's default target also builds its
        # command-line solver and its test programs, and STP runs neither.
        BUILD_COMMAND ${CMAKE_COMMAND} -E chdir <SOURCE_DIR>/build
                      ${CMAKE_MAKE_PROGRAM} libcadical.a
        # No install rules of its own, and the header has to land under the
        # cadical/ directory that <cadical/cadical.hpp> names.
        INSTALL_COMMAND ${CMAKE_COMMAND} -E copy
                        <SOURCE_DIR>/build/libcadical.a
                        <INSTALL_DIR>/lib/${CaDiCaL_ARCHIVE}
        COMMAND ${CMAKE_COMMAND} -E copy <SOURCE_DIR>/src/cadical.hpp
                <INSTALL_DIR>/include/cadical/cadical.hpp
        BUILD_BYPRODUCTS <INSTALL_DIR>/lib/${CaDiCaL_ARCHIVE}
    )
    add_dependencies(deps CaDiCaL-EP)

    set(CADICAL_INCLUDE_DIR "${STP_DEP_DIR}/include")
    set(CADICAL_LIBRARY "${STP_DEP_DIR}/lib/${CaDiCaL_ARCHIVE}")
endif()

set(CaDiCaL_FOUND TRUE)

# Bounded variable addition (--cadical-factor) needs the declare_more_variables
# API. That appeared in CaDiCaL 2.2.0, but the 2.2 line shipped it with
# different contract-checking defaults and was never tested here, so support is
# only compiled in against the 3.x series. Older copies still build and solve;
# STP just warns if the factor flag is explicitly requested.
if(CADICAL_VERSION VERSION_GREATER_EQUAL "3.0.0")
    message(STATUS "CaDiCaL ${CADICAL_VERSION}: bounded variable addition (--cadical-factor) enabled")
    # Mirrored as variables so the test tree can register the factor-forced lit
    # sweep only when the flag can actually engage.
    set(CADICAL_HAS_FACTOR ON)
    # The "inprobing" option arrived in the same 3.0 series. The incremental
    # driver probes for it at run time and simply declines to retire
    # inprocessing without it, so this gates only the tests that assert the
    # retirement happens.
    set(CADICAL_HAS_INPROBING ON)
else()
    message(STATUS "CaDiCaL ${CADICAL_VERSION} predates 3.0.0: --cadical-factor will be unavailable")
    set(CADICAL_HAS_FACTOR OFF)
    set(CADICAL_HAS_INPROBING OFF)
endif()

# UNKNOWN, not STATIC: what was found is whatever CADICAL_DIR or the system
# holds. Both include properties, because only INTERFACE_INCLUDE_DIRECTORIES
# actually adds the directory -- the SYSTEM one just asks for -isystem.
#
# Carrying both the header and the archive on one target is what stops the two
# being made to disagree, which is the failure the CADICAL_DIR note above
# describes.
add_library(CaDiCaL UNKNOWN IMPORTED GLOBAL)
set_target_properties(CaDiCaL PROPERTIES
    IMPORTED_LOCATION "${CADICAL_LIBRARY}"
    INTERFACE_INCLUDE_DIRECTORIES "${CADICAL_INCLUDE_DIR}"
    INTERFACE_SYSTEM_INCLUDE_DIRECTORIES "${CADICAL_INCLUDE_DIR}"
)

mark_as_advanced(CaDiCaL_FOUND)
mark_as_advanced(CaDiCaL_FOUND_SYSTEM)
mark_as_advanced(CADICAL_INCLUDE_DIR)
mark_as_advanced(CADICAL_LIBRARY)
mark_as_advanced(CADICAL_CHECKOUT_DIR)

if(CaDiCaL_FOUND_SYSTEM)
    message(STATUS "Found CaDiCaL ${CADICAL_VERSION}: ${CADICAL_LIBRARY}")
else()
    message(STATUS "Building CaDiCaL ${CADICAL_VERSION}: ${CADICAL_LIBRARY}")
    add_dependencies(CaDiCaL CaDiCaL-EP)
    if(NOT BUILD_SHARED_LIBS)
        install(FILES ${CADICAL_LIBRARY} DESTINATION "${CMAKE_INSTALL_LIBDIR}")
    endif()
endif()

# EOF
