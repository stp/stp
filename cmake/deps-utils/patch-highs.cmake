if(NOT EXISTS "${SOURCE_DIR}/highs/interfaces/highs_c_api.h")
  message(FATAL_ERROR "SOURCE_DIR must name a HiGHS 1.12.0 source tree")
endif()
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
