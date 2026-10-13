# Optional header API, including its pinned Dejavu dependency. The stp branch
# in stp/satsuma carries the CNF sink and CMake install support as commits.
include(deps-helper)

set(SATSUMA_DIR "" CACHE PATH "Prefix of an installed Satsuma CNF output API")
set(Satsuma_FOUND_SYSTEM FALSE)
if(SATSUMA_DIR)
    find_path(SATSUMA_INCLUDE_DIR NAMES satsuma.h
        PATHS "${SATSUMA_DIR}/include/satsuma" "${SATSUMA_DIR}"
        NO_DEFAULT_PATH)
    if(NOT SATSUMA_INCLUDE_DIR)
        message(FATAL_ERROR "SATSUMA_DIR has no installed Satsuma headers: ${SATSUMA_DIR}")
    endif()
    set(Satsuma_FOUND_SYSTEM TRUE)
elseif(NOT STP_DEPS_LOCAL_ONLY)
    find_path(SATSUMA_INCLUDE_DIR NAMES satsuma.h PATH_SUFFIXES satsuma)
    if(SATSUMA_INCLUDE_DIR)
        set(Satsuma_FOUND_SYSTEM TRUE)
    endif()
endif()

if(Satsuma_FOUND_SYSTEM)
    file(STRINGS "${SATSUMA_INCLUDE_DIR}/satsuma.h" _satsuma_api
         REGEX "^#define SATSUMA_CNF_OUTPUT_API 1$")
    if(NOT _satsuma_api OR NOT EXISTS "${SATSUMA_INCLUDE_DIR}/dejavu/dejavu.h")
        message(FATAL_ERROR
            "Satsuma at ${SATSUMA_INCLUDE_DIR} needs CNF output API 1 and Dejavu headers. "
            "Install the stp/satsuma stp branch, or omit SATSUMA_DIR and allow auto-download.")
    endif()
else()
    check_ep_downloaded("Satsuma-EP")
    if(NOT Satsuma-EP_DOWNLOADED)
        check_auto_download("Satsuma" "-DUSE_SATSUMA=OFF" SATSUMA_DIR)
    endif()
    set(SATSUMA_COMMIT "d05d1a17c2d81094bc3e516e8a5e36a79e7c6dd2")
    ExternalProject_Add(Satsuma-EP
        ${STP_EP_COMMON_CONFIG}
        GIT_REPOSITORY https://github.com/stp/satsuma.git
        GIT_TAG ${SATSUMA_COMMIT}
        CMAKE_ARGS ${STP_EP_COMMON_CMAKE_ARGS}
                   -DCMAKE_INSTALL_PREFIX=<INSTALL_DIR>
                   -DSATSUMA_BUILD_CLI=OFF -DSATSUMA_BUILD_TESTING=OFF
                   -DCLIQUES=OFF)
    add_dependencies(deps Satsuma-EP)
    set(SATSUMA_INCLUDE_DIR "${STP_DEP_DIR}/include/satsuma")
    file(MAKE_DIRECTORY "${SATSUMA_INCLUDE_DIR}")
endif()

add_library(Satsuma INTERFACE IMPORTED GLOBAL)
set_target_properties(Satsuma PROPERTIES
    INTERFACE_INCLUDE_DIRECTORIES "${SATSUMA_INCLUDE_DIR}"
    INTERFACE_SYSTEM_INCLUDE_DIRECTORIES "${SATSUMA_INCLUDE_DIR}"
    INTERFACE_COMPILE_FEATURES cxx_std_20)
if(NOT Satsuma_FOUND_SYSTEM)
    add_dependencies(Satsuma Satsuma-EP)
endif()
set(Satsuma_FOUND TRUE)
mark_as_advanced(SATSUMA_INCLUDE_DIR)
