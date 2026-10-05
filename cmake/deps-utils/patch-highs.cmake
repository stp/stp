if(NOT EXISTS "${SOURCE_DIR}/highs/interfaces/highs_c_api.h")
  message(FATAL_ERROR "SOURCE_DIR must name a HiGHS source tree")
endif()
# Keep git apply in the fetched HiGHS tree. When the build directory is inside
# the STP checkout, Git otherwise treats STP as the worktree and silently
# skips every patch path because it is outside the current subdirectory.
get_filename_component(source_parent "${SOURCE_DIR}" DIRECTORY)
set(ENV{GIT_CEILING_DIRECTORIES} "${source_parent}")
set(path "${CMAKE_CURRENT_LIST_DIR}/highs-root-cut-log.patch")
execute_process(COMMAND git apply --reverse --check "${path}"
  WORKING_DIRECTORY "${SOURCE_DIR}"
  RESULT_VARIABLE already OUTPUT_QUIET ERROR_QUIET)
if(NOT already EQUAL 0)
  execute_process(COMMAND git apply "${path}" WORKING_DIRECTORY "${SOURCE_DIR}"
    RESULT_VARIABLE result OUTPUT_VARIABLE output ERROR_VARIABLE error)
  if(NOT result EQUAL 0)
    message(FATAL_ERROR "Cannot apply HiGHS root-cut patch: ${output}${error}")
  endif()
endif()
file(STRINGS "${SOURCE_DIR}/highs/interfaces/highs_c_api.h" stp_highs_cut_version
  REGEX "^#define HIGHS_STP_ROOT_CUT_LOG_VERSION 1$")
if(NOT stp_highs_cut_version)
  message(FATAL_ERROR "HiGHS root-cut patch did not change the source tree")
endif()
