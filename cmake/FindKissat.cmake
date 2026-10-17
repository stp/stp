# The stp branch of stp/kissat adds the incremental API required by STP.
# Follow the dependency lookup and download policy in deps-helper.cmake.
include(deps-helper)

set(KISSAT_DIR "" CACHE PATH
    "Incremental Kissat checkout containing src/kissat.h and build/libkissat.a")
set(_kissat_default_tag "7db70ec5a5f3fd86c5c6fc773ea841ab72dfb4f0")
if(NOT DEFINED CACHE{Kissat_TAG}
   OR "$CACHE{Kissat_TAG}" STREQUAL "$CACHE{_STP_Kissat_TAG_DEFAULT}")
    set(Kissat_TAG "${_kissat_default_tag}" CACHE STRING
        "Commit of stp/kissat to build when Kissat is missing" FORCE)
else()
    set(Kissat_TAG "$CACHE{Kissat_TAG}" CACHE STRING
        "Commit of stp/kissat to build when Kissat is missing")
endif()
set(_STP_Kissat_TAG_DEFAULT "${_kissat_default_tag}" CACHE INTERNAL "")
set(KISSAT_SOURCE_ID "${Kissat_TAG}")
set(Kissat_FOUND_SYSTEM FALSE)

# Re-search so changing KISSAT_DIR or the dependency prefix cannot retain a
# header/library pair from the previous configure.
unset(KISSAT_SOURCE_INCLUDE_DIR CACHE)
unset(KISSAT_LIBRARY CACHE)
if(KISSAT_DIR)
    find_path(KISSAT_SOURCE_INCLUDE_DIR NAMES kissat.h
        PATHS "${KISSAT_DIR}/src" NO_DEFAULT_PATH)
    find_library(KISSAT_LIBRARY NAMES libkissat.a kissat
        PATHS "${KISSAT_DIR}/build" "${KISSAT_DIR}/lib" NO_DEFAULT_PATH)
    if(NOT KISSAT_SOURCE_INCLUDE_DIR OR NOT KISSAT_LIBRARY)
        message(FATAL_ERROR
            "KISSAT_DIR is '${KISSAT_DIR}', but its header and library were not "
            "found. Build that checkout with ./configure -fPIC -fexceptions && make.")
    endif()
    set(Kissat_FOUND_SYSTEM TRUE)
elseif(NOT STP_DEPS_LOCAL_ONLY)
    find_path(KISSAT_SOURCE_INCLUDE_DIR NAMES kissat.h PATH_SUFFIXES kissat)
    find_library(KISSAT_LIBRARY NAMES kissat)
    if(KISSAT_SOURCE_INCLUDE_DIR AND KISSAT_LIBRARY)
        set(Kissat_FOUND_SYSTEM TRUE)

        # Shared installs are immutable to another build. A changed pin can
        # rebuild this build's own install, but must not replace a shared one.
        get_filename_component(_kissat_lib_dir "${KISSAT_LIBRARY}" DIRECTORY)
        get_filename_component(_kissat_lib_dir "${_kissat_lib_dir}" REALPATH)
        get_filename_component(_kissat_dep_dir "${STP_DEP_DIR}" REALPATH)
        string(FIND "${_kissat_lib_dir}/" "${_kissat_dep_dir}/" _kissat_in_deps)
        if(_kissat_in_deps EQUAL 0)
            set(_kissat_recorded "")
            if(EXISTS "${_kissat_lib_dir}/kissat-source.txt")
                file(READ "${_kissat_lib_dir}/kissat-source.txt" _kissat_recorded)
                string(STRIP "${_kissat_recorded}" _kissat_recorded)
            endif()
            if(NOT _kissat_recorded STREQUAL KISSAT_SOURCE_ID)
                get_filename_component(_kissat_binary_dir "${PROJECT_BINARY_DIR}" REALPATH)
                string(FIND "${_kissat_dep_dir}/" "${_kissat_binary_dir}/" _kissat_local)
                if(NOT _kissat_local EQUAL 0)
                    message(FATAL_ERROR
                        "The Kissat in ${_kissat_lib_dir} does not match ${Kissat_TAG}. "
                        "STP_DEP_DIR is shared, so it will not be overwritten. "
                        "Give this build its own dependency directory with -USTP_DEP_DIR, "
                        "or remove the old Kissat install before rebuilding it.")
                endif()
                message(STATUS "Kissat source revision changed: rebuilding the local install")
                set(Kissat_FOUND_SYSTEM FALSE)
                file(GLOB _kissat_configure_stamps
                    "${STP_DEPS_PREFIX}/src/Kissat-EP-stamp/Kissat-EP-configure"
                    "${STP_DEPS_PREFIX}/src/Kissat-EP-stamp/*/Kissat-EP-configure")
                if(_kissat_configure_stamps)
                    file(REMOVE ${_kissat_configure_stamps})
                endif()
            endif()
        endif()
    endif()
endif()

if(Kissat_FOUND_SYSTEM)
    set(KISSAT_INCLUDE_DIR "${PROJECT_BINARY_DIR}/deps/kissat-include")
    configure_file("${KISSAT_SOURCE_INCLUDE_DIR}/kissat.h"
        "${KISSAT_INCLUDE_DIR}/kissat/kissat.h" COPYONLY)
    set(_kissat_probe "${PROJECT_BINARY_DIR}/kissat-incremental.cpp")
    file(WRITE "${_kissat_probe}"
        "extern \"C\" {\n#include <kissat/kissat.h>\n}\n#include <cstdio>\n#include <cstdlib>\n"
        "#ifndef KISSAT_HAS_INCREMENTAL\n#error incremental Kissat required\n#endif\n"
        "#ifndef KISSAT_HAS_INCREMENTAL_GREEDY\n#error incremental greedy Kissat required\n#endif\n"
        "int main() { const kissat_allocator a = {nullptr, "
        "[](void*, size_t n) { return std::malloc(n); }, "
        "[](void*, void *p, size_t n) { return std::realloc(p, n); }, "
        "[](void*, void *p) { std::free(p); }}; "
        "kissat *s = kissat_init_with_allocator(&a); "
        "kissat_set_option(s, \"quiet\", 1); "
        "kissat_set_option(s, \"incremental\", 1); "
        "kissat_set_option(s, \"incrementalreuse\", 2); "
        "if (kissat_get_option(s, \"incrementallucky\") != 0 || "
        "kissat_get_option(s, \"incrementalluckyinit\") != 100 || "
        "kissat_get_option(s, \"incrementalluckydecisions\") != 10000 || "
        "kissat_get_option(s, \"incrementalluckygrowth\") != 4 || "
        "kissat_get_option(s, \"incrementalluckyphasecache\") != 0) return 6; "
        "if (kissat_get_option(s, \"incremental\") != 1 || "
        "kissat_get_option(s, \"incrementalreuse\") != 2) return 1; "
        "kissat_add(s, 1); kissat_add(s, 0); "
        "if (kissat_solve(s) != 10) return 2; kissat_assume(s, -1); "
        "if (kissat_solve(s) != 20 || !kissat_failed(s, -1) || "
        "kissat_inconsistent(s)) return 3; "
        "if (kissat_solve(s) != 10) return 4; "
        "kissat_add(s, 2); kissat_add(s, 0); "
        "if (kissat_solve(s) != 10 || kissat_value(s, 2) != 2) return 5; "
        "kissat_protect(s, 1); kissat_unprotect(s, 1); "
        "kissat_maximum_variable(s); kissat_set_phase(s, 1); "
        "std::puts(kissat_version()); kissat_release(s); return 0; }\n")
    set(_kissat_libraries "${KISSAT_LIBRARY}")
    if(UNIX)
        list(APPEND _kissat_libraries m)
    endif()
    unset(KISSAT_INCREMENTAL_API CACHE)
    unset(KISSAT_INCREMENTAL_RUN CACHE)
    if(CMAKE_CROSSCOMPILING)
        try_compile(KISSAT_INCREMENTAL_API
            "${PROJECT_BINARY_DIR}/kissat-probe" "${_kissat_probe}"
            CMAKE_FLAGS "-DINCLUDE_DIRECTORIES=${KISSAT_INCLUDE_DIR}"
            LINK_LIBRARIES ${_kissat_libraries}
            OUTPUT_VARIABLE _kissat_probe_output)
        set(KISSAT_INCREMENTAL_RUN 0)
    else()
        try_run(KISSAT_INCREMENTAL_RUN KISSAT_INCREMENTAL_API
            "${PROJECT_BINARY_DIR}/kissat-probe" "${_kissat_probe}"
            CMAKE_FLAGS "-DINCLUDE_DIRECTORIES=${KISSAT_INCLUDE_DIR}"
            LINK_LIBRARIES ${_kissat_libraries}
            COMPILE_OUTPUT_VARIABLE _kissat_probe_output
            RUN_OUTPUT_VARIABLE KISSAT_VERSION)
        string(STRIP "${KISSAT_VERSION}" KISSAT_VERSION)
    endif()
    if(NOT KISSAT_INCREMENTAL_API OR NOT KISSAT_INCREMENTAL_RUN EQUAL 0)
        if(KISSAT_DIR)
            message(FATAL_ERROR
                "Kissat in KISSAT_DIR lacks the incremental API STP requires. "
                "Use the stp branch of https://github.com/stp/kissat.\n"
                "${_kissat_probe_output}")
        endif()
        message(STATUS "Installed Kissat lacks STP's incremental API: building the fork")
        set(Kissat_FOUND_SYSTEM FALSE)
    endif()
endif()

if(NOT Kissat_FOUND_SYSTEM)
    check_ep_downloaded("Kissat-EP")
    if(NOT Kissat-EP_DOWNLOADED)
        check_auto_download("Kissat" "-DUSE_KISSAT=OFF")
    endif()
    set(Kissat_ARCHIVE "${CMAKE_STATIC_LIBRARY_PREFIX}kissat${CMAKE_STATIC_LIBRARY_SUFFIX}")
    set(_kissat_source_file "${STP_DEPS_PREFIX}/kissat-source.txt")
    file(WRITE "${_kissat_source_file}" "${KISSAT_SOURCE_ID}\n")
    set(_kissat_disconnected ON)
    set(_kissat_checkout "${STP_DEPS_PREFIX}/src/Kissat-EP")
    if(EXISTS "${_kissat_checkout}/.git")
        find_package(Git REQUIRED)
        execute_process(COMMAND "${GIT_EXECUTABLE}" cat-file -e "${Kissat_TAG}^{commit}"
            WORKING_DIRECTORY "${_kissat_checkout}"
            RESULT_VARIABLE _kissat_revision_available OUTPUT_QUIET ERROR_QUIET)
        if(NOT _kissat_revision_available EQUAL 0)
            # A moved pin may need a fetch. Disconnected updates cannot
            # acquire a commit that was published after this clone was made.
            set(_kissat_disconnected OFF)
            message(STATUS "Fetching the new Kissat revision ${Kissat_TAG}")
        endif()
    endif()
    # After an existing install is updated, reconfigure and adopt that
    # completed install. This also removes a connected update from subsequent
    # builds. Watch only an existing record to avoid a missing-file loop.
    if(EXISTS "${STP_DEP_DIR}/lib/kissat-source.txt")
        set_property(DIRECTORY APPEND PROPERTY CMAKE_CONFIGURE_DEPENDS
            "${STP_DEP_DIR}/lib/kissat-source.txt")
    endif()
    set(_kissat_ep_config ${STP_EP_COMMON_CONFIG})
    list(FIND _kissat_ep_config UPDATE_DISCONNECTED _kissat_update_index)
    math(EXPR _kissat_update_index "${_kissat_update_index} + 1")
    list(REMOVE_AT _kissat_ep_config ${_kissat_update_index})
    list(INSERT _kissat_ep_config ${_kissat_update_index} ${_kissat_disconnected})
    ExternalProject_Add(Kissat-EP
        ${_kissat_ep_config}
        GIT_REPOSITORY https://github.com/stp/kissat
        GIT_TAG ${Kissat_TAG}
        CMAKE_ARGS ${STP_EP_COMMON_CMAKE_ARGS}
            -DCMAKE_INSTALL_PREFIX=<INSTALL_DIR>
            -DCMAKE_INSTALL_LIBDIR=lib
            -DBUILD_SHARED_LIBS=OFF
            -DBUILD_TESTING=OFF
            -DKISSAT_BUILD_CLI=OFF
            -DKISSAT_IDENTIFIER=${Kissat_TAG}
        INSTALL_COMMAND ${CMAKE_COMMAND} --build <BINARY_DIR> --target install
            --config $<IF:$<BOOL:$<CONFIG>>,$<CONFIG>,Release>
            COMMAND ${CMAKE_COMMAND} -E copy "${_kissat_source_file}"
                <INSTALL_DIR>/lib/kissat-source.txt
        BUILD_BYPRODUCTS <INSTALL_DIR>/lib/${Kissat_ARCHIVE}
    )
    add_dependencies(deps Kissat-EP)
    set(KISSAT_INCLUDE_DIR "${STP_DEP_DIR}/include")
    set(KISSAT_LIBRARY "${STP_DEP_DIR}/lib/${Kissat_ARCHIVE}")
    message(STATUS "Building incremental Kissat ${Kissat_TAG}: ${KISSAT_LIBRARY}")
else()
    message(STATUS "Found incremental Kissat ${KISSAT_VERSION}: ${KISSAT_LIBRARY}")
endif()

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(Kissat REQUIRED_VARS KISSAT_INCLUDE_DIR KISSAT_LIBRARY)
add_library(Kissat UNKNOWN IMPORTED GLOBAL)
set_target_properties(Kissat PROPERTIES
    IMPORTED_LOCATION "${KISSAT_LIBRARY}"
    INTERFACE_INCLUDE_DIRECTORIES "${KISSAT_INCLUDE_DIR}"
    INTERFACE_SYSTEM_INCLUDE_DIRECTORIES "${KISSAT_INCLUDE_DIR}")
if(UNIX)
    set_target_properties(Kissat PROPERTIES INTERFACE_LINK_LIBRARIES m)
endif()
if(NOT Kissat_FOUND_SYSTEM)
    add_dependencies(Kissat Kissat-EP)
endif()

# Learned-clause exchange and post-load diversification: also an STP
# extension on the fork, which stp-p's group can run on. Probed for a Kissat
# that was not built here; the pinned commit carries it.
unset(KISSAT_HAS_CLAUSE_EXCHANGE CACHE)
if(Kissat_FOUND_SYSTEM)
    set(_kissat_exchange_probe "${PROJECT_BINARY_DIR}/kissat-exchange.cpp")
    file(WRITE "${_kissat_exchange_probe}"
        "extern \"C\" {\n#include <kissat/kissat.h>\n}\n"
        "#ifndef KISSAT_HAS_CLAUSE_EXCHANGE\n#error no clause exchange\n#endif\n"
        "int main() { kissat *s = kissat_init(); kissat_import_statistics i; "
        "kissat_set_learn(s, nullptr, 0, nullptr); "
        "kissat_set_import(s, nullptr, 0, nullptr, nullptr); "
        "kissat_diversify(s, 0, 2, 0); kissat_get_import_statistics(s, &i); "
        "kissat_release(s); return (int) i.polls; }\n")
    try_compile(KISSAT_HAS_CLAUSE_EXCHANGE
        "${PROJECT_BINARY_DIR}/kissat-exchange-probe" "${_kissat_exchange_probe}"
        CMAKE_FLAGS "-DINCLUDE_DIRECTORIES=${KISSAT_INCLUDE_DIR}"
        LINK_LIBRARIES ${_kissat_libraries})
else()
    set(KISSAT_HAS_CLAUSE_EXCHANGE ON)
endif()
message(STATUS "Kissat clause exchange: ${KISSAT_HAS_CLAUSE_EXCHANGE}")

mark_as_advanced(Kissat_TAG KISSAT_SOURCE_INCLUDE_DIR KISSAT_LIBRARY KISSAT_INCREMENTAL_API)
