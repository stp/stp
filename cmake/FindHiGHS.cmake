# Optional advisory LP engine. Follow the same installed/auto-download policy
# as the other private dependencies; the exact certificate checker is STP's.
include(deps-helper)
set(HIGHS_DIR "" CACHE PATH "Prefix of an installed HiGHS library")
if(HIGHS_DIR)
  find_path(HIGHS_INCLUDE_DIR interfaces/highs_c_api.h
    PATHS "${HIGHS_DIR}/include/highs" NO_DEFAULT_PATH)
  find_library(HIGHS_LIBRARY NAMES highs PATHS "${HIGHS_DIR}/lib" "${HIGHS_DIR}/lib64" NO_DEFAULT_PATH)
  if(NOT HIGHS_INCLUDE_DIR OR NOT HIGHS_LIBRARY)
    message(FATAL_ERROR "HIGHS_DIR must name a built and installed HiGHS prefix")
  endif()
elseif(NOT STP_DEPS_LOCAL_ONLY)
  find_path(HIGHS_INCLUDE_DIR interfaces/highs_c_api.h PATH_SUFFIXES highs)
  find_library(HIGHS_LIBRARY NAMES highs)
endif()
if(NOT HIGHS_INCLUDE_DIR OR NOT HIGHS_LIBRARY)
  check_ep_downloaded("HiGHS-EP")
  if(NOT HiGHS-EP_DOWNLOADED)
    check_auto_download("HiGHS" "-DENABLE_HIGHS=OFF")
  endif()
  set(HIGHS_INCLUDE_DIR "${STP_DEP_DIR}/include/highs")
  set(HIGHS_LIBRARY "${STP_DEP_DIR}/lib/${CMAKE_STATIC_LIBRARY_PREFIX}highs${CMAKE_STATIC_LIBRARY_SUFFIX}")
  file(MAKE_DIRECTORY "${HIGHS_INCLUDE_DIR}")
  set(stp_highs_patch_args)
  if(ENABLE_HIGHS_CUT_LOG)
    set(stp_highs_patch_args PATCH_COMMAND ${CMAKE_COMMAND}
      "-DSOURCE_DIR=<SOURCE_DIR>" -P "${CMAKE_CURRENT_LIST_DIR}/deps-utils/patch-highs.cmake")
  endif()
  set(stp_highs_assert_args)
  if(ENABLE_ASSERTIONS)
    # STP strips NDEBUG from its configuration flags, but HiGHS configures
    # separately and would restore it, hiding assertion-only regressions.
    string(TOUPPER "${CMAKE_BUILD_TYPE}" stp_highs_config)
    set(stp_highs_c_flags "CMAKE_C_FLAGS_${stp_highs_config}")
    set(stp_highs_cxx_flags "CMAKE_CXX_FLAGS_${stp_highs_config}")
    list(APPEND stp_highs_assert_args
      "-D${stp_highs_c_flags}:STRING=${${stp_highs_c_flags}}"
      "-D${stp_highs_cxx_flags}:STRING=${${stp_highs_cxx_flags}}")
  endif()
  ExternalProject_Add(HiGHS-EP ${STP_EP_COMMON_CONFIG}
    URL https://codeload.github.com/ERGO-Code/HiGHS/tar.gz/38e323294bd29e15f5e6cdfb07021a4f8bd9dc52
    URL_HASH SHA256=ec5b6fe5f34f62699fb810eb0ec9022bf77a6b24cc3b6c8cd2162f76098caf90
    ${stp_highs_patch_args}
    CMAKE_ARGS ${STP_EP_COMMON_CMAKE_ARGS} ${stp_highs_assert_args}
      -DCMAKE_INSTALL_PREFIX=<INSTALL_DIR> -DCMAKE_INSTALL_LIBDIR=lib
      -DBUILD_SHARED_LIBS=OFF -DBUILD_TESTING=OFF -DBUILD_EXAMPLES=OFF
      -DBUILD_CXX_EXE=OFF -DZLIB=OFF -DHIGHS_NO_DEFAULT_THREADS=ON
    BUILD_BYPRODUCTS "${HIGHS_LIBRARY}")
  add_dependencies(deps HiGHS-EP)
endif()
if(ENABLE_HIGHS_CUT_LOG AND NOT TARGET HiGHS-EP)
  file(STRINGS "${HIGHS_INCLUDE_DIR}/interfaces/highs_c_api.h" stp_highs_cut_version
    REGEX "^#define HIGHS_STP_ROOT_CUT_LOG_VERSION 1$")
  if(NOT stp_highs_cut_version)
    message(FATAL_ERROR "ENABLE_HIGHS_CUT_LOG requires HiGHS rebuilt with cmake/deps-utils/highs-root-cut-log.patch")
  endif()
endif()
add_library(HiGHS UNKNOWN IMPORTED GLOBAL)
set_target_properties(HiGHS PROPERTIES IMPORTED_LOCATION "${HIGHS_LIBRARY}"
  INTERFACE_INCLUDE_DIRECTORIES "${HIGHS_INCLUDE_DIR}"
  INTERFACE_SYSTEM_INCLUDE_DIRECTORIES "${HIGHS_INCLUDE_DIR}")
if(TARGET HiGHS-EP)
  add_dependencies(HiGHS HiGHS-EP)
endif()
set(HiGHS_FOUND TRUE)
message(STATUS "HiGHS advisory LP engine: ${HIGHS_LIBRARY}")
