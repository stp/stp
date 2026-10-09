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
#   CADICAL_HAS_DECISION_POLARITY  decision-time polarity advice is available
#
# CADICAL_DIR names a CaDiCaL checkout -- the directory holding src/cadical.hpp
# with build/libcadical.a beneath it -- and is rung 0 of the ladder in
# cmake/deps-helper.cmake.

include(deps-helper)

set(CADICAL_DIR "" CACHE PATH
    "Path to a CaDiCaL checkout: the directory containing src/cadical.hpp, with build/libcadical.a beneath it")

set(CaDiCaL_FOUND_SYSTEM FALSE)
set(CADICAL_VERSION "unknown")

# The CaDiCaL patch set STP carries, as one hash: the patch step records it in
# the checkout and the install, so that a changed set is applied again to an
# existing checkout and an install built from another set is not adopted. The
# files are configure dependencies, so an edit to one -- committed or not --
# re-runs CMake, which hashes the set again.
set(_cadical_patch_files)
file(GLOB _cadical_patch_files CONFIGURE_DEPENDS
     "${CMAKE_CURRENT_LIST_DIR}/deps-utils/cadical-*.patch"
     "${CMAKE_CURRENT_LIST_DIR}/deps-utils/patch-cadical.cmake"
     "${CMAKE_CURRENT_LIST_DIR}/deps-utils/cadical-CMakeLists.txt")
list(SORT _cadical_patch_files)
set(_cadical_patch_hashes "")
foreach(_file ${_cadical_patch_files})
    file(SHA256 "${_file}" _hash)
    string(APPEND _cadical_patch_hashes "${_hash}")
endforeach()
string(SHA256 CADICAL_PATCH_SET "${_cadical_patch_hashes}")
set_property(DIRECTORY APPEND PROPERTY CMAKE_CONFIGURE_DEPENDS ${_cadical_patch_files})

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
elseif(NOT STP_DEPS_LOCAL_ONLY)
    # Rung 1, which STP_DEPS_LOCAL_ONLY skips. Includes a CaDiCaL that another
    # build directory installed into STP_DEP_DIR.
    find_path(CADICAL_INCLUDE_DIR NAMES cadical/cadical.hpp)
    find_library(CADICAL_LIBRARY NAMES cadical)
    # A CaDiCaL this build installed into STP_DEP_DIR carries the patch set it
    # was built with; one built from another set, or before sets were
    # recorded, is not adopted. Inside this build directory (STP_DEP_DIR's
    # default) it is this tree's own and is built again. Outside it, other
    # build directories may be using it, and building it again would change
    # their CaDiCaL underneath them: configure stops instead.
    if(CADICAL_LIBRARY AND STP_DEP_DIR)
        get_filename_component(_cadical_lib_dir "${CADICAL_LIBRARY}" DIRECTORY)
        get_filename_component(_cadical_lib_dir "${_cadical_lib_dir}" REALPATH)
        get_filename_component(_stp_dep_dir "${STP_DEP_DIR}" REALPATH)
        string(FIND "${_cadical_lib_dir}/" "${_stp_dep_dir}/" _in_dep_dir)
        if(_in_dep_dir EQUAL 0)
            set(_cadical_recorded "")
            if(EXISTS "${_cadical_lib_dir}/cadical-patch-set.txt")
                file(READ "${_cadical_lib_dir}/cadical-patch-set.txt" _cadical_recorded)
                string(STRIP "${_cadical_recorded}" _cadical_recorded)
            endif()
            if(NOT _cadical_recorded STREQUAL CADICAL_PATCH_SET)
                get_filename_component(_stp_binary_dir "${PROJECT_BINARY_DIR}" REALPATH)
                string(FIND "${_stp_dep_dir}/" "${_stp_binary_dir}/" _dep_dir_here)
                if(NOT _dep_dir_here EQUAL 0)
                    message(FATAL_ERROR
                        "The CaDiCaL in ${_cadical_lib_dir} was built from another "
                        "STP patch set, and STP_DEP_DIR (${STP_DEP_DIR}) is outside "
                        "this build directory, so other build directories may be "
                        "using it. Either give this build directory a dependency "
                        "directory of its own (configure with -USTP_DEP_DIR for "
                        "the default, ${STP_DEPS_PREFIX}/install), or remove that "
                        "CaDiCaL alone -- ${_cadical_lib_dir}/libcadical.a, "
                        "${_cadical_lib_dir}/cadical-patch-set.txt and "
                        "${STP_DEP_DIR}/include/cadical -- so that it is built "
                        "again from this patch set; the other dependencies there "
                        "stay.")
                endif()
                message(STATUS "CaDiCaL in ${_cadical_lib_dir} was built from "
                               "another patch set: building it again")
                # This tree's stamps say the old set was patched in. Without
                # them the patch step runs again, and every step after it:
                # 'patch', or 'patch_disconnected' from CMake 3.27 on (with
                # UPDATE_DISCONNECTED), in a per-configuration directory for a
                # multi-config generator. CMake from 3.27 would also rerun it
                # for its changed command (the set's hash is in it); before
                # 3.27 only the missing stamp does.
                set(_cadical_stamps "${STP_DEPS_PREFIX}/src/CaDiCaL-EP-stamp")
                file(GLOB _cadical_patch_stamps
                     "${_cadical_stamps}/CaDiCaL-EP-patch"
                     "${_cadical_stamps}/CaDiCaL-EP-patch_disconnected"
                     "${_cadical_stamps}/*/CaDiCaL-EP-patch"
                     "${_cadical_stamps}/*/CaDiCaL-EP-patch_disconnected")
                if(_cadical_patch_stamps)
                    file(REMOVE ${_cadical_patch_stamps})
                endif()
                unset(CADICAL_INCLUDE_DIR CACHE)
                unset(CADICAL_LIBRARY CACHE)
                set(CADICAL_INCLUDE_DIR "")
                set(CADICAL_LIBRARY "")
            endif()
        endif()
    endif()
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

    # CaDiCaL has no CMake of its own, so it is given one -- see
    # cmake/deps-utils/cadical-CMakeLists.txt for why driving its configure
    # script instead does not survive a Windows host.
    #
    # Only libcadical: CaDiCaL's default target also builds its command-line
    # solver and its model-based tester, and STP runs neither.
    ExternalProject_Add(
        CaDiCaL-EP
        ${STP_EP_COMMON_CONFIG}
        GIT_REPOSITORY https://github.com/arminbiere/cadical
        GIT_TAG ${CaDiCaL_TAG}
        PATCH_COMMAND ${CMAKE_COMMAND} "-DSOURCE_DIR=<SOURCE_DIR>"
                      "-DCADICAL_VERSION=${CADICAL_VERSION}"
                      "-DSTP_PATCH_SET=${CADICAL_PATCH_SET}"
                      -P "${CMAKE_CURRENT_LIST_DIR}/deps-utils/patch-cadical.cmake"
        CMAKE_ARGS ${STP_EP_COMMON_CMAKE_ARGS}
                   -DCMAKE_INSTALL_PREFIX=<INSTALL_DIR>
                   -DCMAKE_INSTALL_LIBDIR=lib
                   -DCADICAL_VERSION=${CADICAL_VERSION}
                   -DCADICAL_IDENTIFIER=${CaDiCaL_TAG}
        BUILD_BYPRODUCTS <INSTALL_DIR>/lib/${CaDiCaL_ARCHIVE}
    )
    add_dependencies(deps CaDiCaL-EP)

    set(CADICAL_INCLUDE_DIR "${STP_DEP_DIR}/include")
    set(CADICAL_LIBRARY "${STP_DEP_DIR}/lib/${CaDiCaL_ARCHIVE}")
endif()

set(CaDiCaL_FOUND TRUE)

# This is an STP extension, not a version-derived upstream capability. Link
# a probe so a new header paired with an old archive cannot silently turn
# requested polarity advice into a no-op. Bundled builds apply the patch, which
# is written against the 3.x line -- deps-utils/patch-cadical.cmake leaves a
# 2.x CaDiCaL without it, from the same CADICAL_VERSION as this test.
if(CaDiCaL_FOUND_SYSTEM)
    set(_polarity_src "${PROJECT_BINARY_DIR}/CaDiCaL_polarity.cpp")
    file(WRITE "${_polarity_src}"
         "#include <cadical/cadical.hpp>\n"
         "int main() { CaDiCaL::Solver s; s.disconnect_decision_polarity_advisor(); }\n")
    set(_polarity_libraries ${CADICAL_LIBRARY})
    if(WIN32)
        list(APPEND _polarity_libraries psapi)
    endif()
    try_compile(CADICAL_HAS_DECISION_POLARITY
                "${PROJECT_BINARY_DIR}/CaDiCaL_polarity_probe" "${_polarity_src}"
                CMAKE_FLAGS "-DINCLUDE_DIRECTORIES=${CADICAL_INCLUDE_DIR}"
                LINK_LIBRARIES ${_polarity_libraries})
elseif(CADICAL_VERSION VERSION_GREATER_EQUAL "3.0.0")
    set(CADICAL_HAS_DECISION_POLARITY ON)
else()
    set(CADICAL_HAS_DECISION_POLARITY OFF)
endif()
message(STATUS "CaDiCaL decision-time polarity advice: ${CADICAL_HAS_DECISION_POLARITY}")

# Clause import and post-load diversification: also an STP extension
# (cadical-clause-import.patch), probed the same way for a CaDiCaL that was
# not built here. A copy patched before the per-poll import budget existed
# counts as without it.
if(CaDiCaL_FOUND_SYSTEM)
    set(_import_src "${PROJECT_BINARY_DIR}/CaDiCaL_import.cpp")
    file(WRITE "${_import_src}"
         "#include <cadical/cadical.hpp>\n"
         "struct I : CaDiCaL::ClauseImporter { int import_budget () override "
         "{ return 1; } bool import_clause (std::vector<int> &) override "
         "{ return false; } };\n"
         "int main() { CaDiCaL::Solver s; I i; s.connect_clause_importer(&i); "
         "s.disconnect_clause_importer(); "
         "s.diversify(0, 2, false); return (int) s.import_statistics().polls; }\n")
    try_compile(CADICAL_HAS_CLAUSE_IMPORT
                "${PROJECT_BINARY_DIR}/CaDiCaL_import_probe" "${_import_src}"
                CMAKE_FLAGS "-DINCLUDE_DIRECTORIES=${CADICAL_INCLUDE_DIR}"
                LINK_LIBRARIES ${_polarity_libraries})
elseif(CADICAL_VERSION VERSION_GREATER_EQUAL "3.0.0")
    set(CADICAL_HAS_CLAUSE_IMPORT ON)
else()
    set(CADICAL_HAS_CLAUSE_IMPORT OFF)
endif()
message(STATUS "CaDiCaL clause import: ${CADICAL_HAS_CLAUSE_IMPORT}")

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

# CaDiCaL reads its own resource usage through GetProcessMemoryInfo on
# Windows, which lives in the Process Status API. Without naming it here, a
# static link of STP fails on an unresolved symbol that says nothing about
# CaDiCaL.
if(WIN32)
    set_target_properties(CaDiCaL PROPERTIES
        IMPORTED_LINK_INTERFACE_LIBRARIES psapi)
endif()

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
endif()

# EOF
