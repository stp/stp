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

# What is built when CaDiCaL has to be built: a commit of stp/cadical, whose
# `stp` branch is CaDiCaL 3.0.1 with the changes STP needs on it as commits --
# generated cubes in external literal numbering, a witness-marked variable
# restored when it becomes observed, decision polarity advice, clause import
# and search diversification -- and a CMake build of the library, which
# keeps GCC's bitfield layout under MinGW. Its `stp-2.1.3` branch is the same
# build, and the witness fix, on 2.1.3.
#
# The version is kept separate from the source revision, because the feature
# gates below are decided from a release number rather than a hash. Naming a
# commit of another line means naming its version too.
#
# Both are cache entries so that they can be chosen, but one an earlier
# configure merely defaulted to is not a choice: it follows the default when
# the default moves, where a value given with -D is kept. Without that, a build
# directory would go on building whatever revision was the default when it was
# first configured. The two revisions this defaulted to before STP's changes
# moved into the fork count as defaults: neither carries the build this needs.
set(_cadical_former_defaults
    "rel-3.0.1" "17ababb48ecb0e5d61f45e941ebbd8b59312fff5")
macro(_stp_cadical_default var value doc)
    if(NOT DEFINED CACHE{${var}}
       OR "$CACHE{${var}}" STREQUAL "$CACHE{_STP_${var}_DEFAULT}"
       OR (NOT DEFINED CACHE{_STP_${var}_DEFAULT}
           AND "$CACHE{${var}}" IN_LIST _cadical_former_defaults))
        set(${var} "${value}" CACHE STRING "${doc}" FORCE)
    else()
        # A choice, kept. This only gives a -D without a type its type.
        set(${var} "$CACHE{${var}}" CACHE STRING "${doc}")
    endif()
    set(_STP_${var}_DEFAULT "${value}" CACHE INTERNAL "")
endmacro()
_stp_cadical_default(CaDiCaL_TAG "a86f08a4e39aeed296f3b0f4beed3a7f8c1c3a43"
    "Commit (or tag) of stp/cadical to build when one has to be built")
_stp_cadical_default(CaDiCaL_VERSION "3.0.1"
    "Release version of the CaDiCaL that CaDiCaL_TAG names")
mark_as_advanced(CaDiCaL_TAG CaDiCaL_VERSION)

# What a CaDiCaL built here was built from. The install records it beside the
# archive, so that an install built from another revision -- an earlier pin,
# in a dependency directory several build directories share -- is not adopted.
set(CADICAL_SOURCE_ID "${CaDiCaL_TAG};${CaDiCaL_VERSION}")

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
    # A CaDiCaL this build installed into STP_DEP_DIR records the revision it
    # was built from; one built from another, or before revisions were
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
            if(EXISTS "${_cadical_lib_dir}/cadical-source.txt")
                file(READ "${_cadical_lib_dir}/cadical-source.txt" _cadical_recorded)
                string(STRIP "${_cadical_recorded}" _cadical_recorded)
            endif()
            if(NOT _cadical_recorded STREQUAL CADICAL_SOURCE_ID)
                get_filename_component(_stp_binary_dir "${PROJECT_BINARY_DIR}" REALPATH)
                string(FIND "${_stp_dep_dir}/" "${_stp_binary_dir}/" _dep_dir_here)
                if(NOT _dep_dir_here EQUAL 0)
                    message(FATAL_ERROR
                        "The CaDiCaL in ${_cadical_lib_dir} was built from another "
                        "revision than ${CaDiCaL_TAG}, and STP_DEP_DIR "
                        "(${STP_DEP_DIR}) is outside this build directory, so "
                        "other build directories may be using it. Either give "
                        "this build directory a dependency directory of its own "
                        "(configure with -USTP_DEP_DIR for the default, "
                        "${STP_DEPS_PREFIX}/install), or remove that CaDiCaL "
                        "alone -- ${_cadical_lib_dir}/libcadical.a, "
                        "${_cadical_lib_dir}/cadical-source.txt and "
                        "${STP_DEP_DIR}/include/cadical -- so that it is built "
                        "again from this revision; the other dependencies there "
                        "stay.")
                endif()
                message(STATUS "CaDiCaL in ${_cadical_lib_dir} was built from "
                               "another revision: building it again")
                # A changed revision downloads again by itself, and every step
                # after the download runs again behind it. What does not is an
                # install that merely lacks the record -- one made before
                # revisions were recorded -- from the revision this tree's
                # stamps already say is configured and installed. Without the
                # configure stamp, configure, build and install run again, and
                # the install writes the record. Per configuration directory
                # too, for a multi-config generator.
                set(_cadical_stamps "${STP_DEPS_PREFIX}/src/CaDiCaL-EP-stamp")
                file(GLOB _cadical_configure_stamps
                     "${_cadical_stamps}/CaDiCaL-EP-configure"
                     "${_cadical_stamps}/*/CaDiCaL-EP-configure")
                if(_cadical_configure_stamps)
                    file(REMOVE ${_cadical_configure_stamps})
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

    set(CADICAL_VERSION "${CaDiCaL_VERSION}")

    set(CaDiCaL_ARCHIVE
        "${CMAKE_STATIC_LIBRARY_PREFIX}cadical${CMAKE_STATIC_LIBRARY_SUFFIX}")

    # The record the install leaves beside the archive (see rung 1). Written
    # into this build directory's own scratch tree, never into STP_DEP_DIR:
    # only a finished install may say what STP_DEP_DIR holds.
    set(_cadical_source_file "${STP_DEPS_PREFIX}/cadical-source.txt")
    file(WRITE "${_cadical_source_file}" "${CADICAL_SOURCE_ID}\n")

    # A clone rather than a tarball, because CaDiCaL_TAG may name any commit
    # or tag of the fork, and a tarball would need its checksum named too.
    #
    # The fork's own CMake build is a library and a header and nothing else:
    # CaDiCaL's configure script cannot run on a native Windows host, which is
    # why it has one. The version and the identifier are passed because what
    # was cloned is known here; the build reads both itself otherwise.
    ExternalProject_Add(
        CaDiCaL-EP
        ${STP_EP_COMMON_CONFIG}
        GIT_REPOSITORY https://github.com/stp/cadical
        GIT_TAG ${CaDiCaL_TAG}
        CMAKE_ARGS ${STP_EP_COMMON_CMAKE_ARGS}
                   -DCMAKE_INSTALL_PREFIX=<INSTALL_DIR>
                   -DCMAKE_INSTALL_LIBDIR=lib
                   -DCADICAL_VERSION=${CADICAL_VERSION}
                   -DCADICAL_IDENTIFIER=${CaDiCaL_TAG}
        INSTALL_COMMAND ${CMAKE_COMMAND} --build <BINARY_DIR> --target install
                                         --config $<CONFIG>
                COMMAND ${CMAKE_COMMAND} -E copy "${_cadical_source_file}"
                        <INSTALL_DIR>/lib/cadical-source.txt
        BUILD_BYPRODUCTS <INSTALL_DIR>/lib/${CaDiCaL_ARCHIVE}
    )
    add_dependencies(deps CaDiCaL-EP)

    set(CADICAL_INCLUDE_DIR "${STP_DEP_DIR}/include")
    set(CADICAL_LIBRARY "${STP_DEP_DIR}/lib/${CaDiCaL_ARCHIVE}")
endif()

set(CaDiCaL_FOUND TRUE)

# This is an STP extension, not a version-derived upstream capability. Link
# a probe so a new header paired with an old archive cannot silently turn
# requested polarity advice into a no-op. A CaDiCaL built here has it on the
# 3.x line -- the fork's `stp` branch carries it, `stp-2.1.3` does not -- so
# there it follows from CADICAL_VERSION.
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

# Clause import and post-load diversification: also an STP extension, on the
# fork's `stp` branch, and probed the same way for a CaDiCaL that was not
# built here. A copy carrying the extension from before the per-poll import
# budget existed counts as without it.
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
