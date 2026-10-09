# ExternalProject may repeat this step against an already patched checkout.
if(NOT EXISTS "${SOURCE_DIR}/src/misc/util/abc_global.h")
    message(FATAL_ERROR "SOURCE_DIR must name an ABC checkout")
endif()

set(patch "${CMAKE_CURRENT_LIST_DIR}/abc-checked-allocations.patch")
execute_process(
    COMMAND git apply --unidiff-zero --reverse --check "${patch}"
    WORKING_DIRECTORY "${SOURCE_DIR}"
    RESULT_VARIABLE already_applied OUTPUT_QUIET ERROR_QUIET)
if(NOT already_applied EQUAL 0)
    execute_process(
        COMMAND git apply --unidiff-zero "${patch}"
        WORKING_DIRECTORY "${SOURCE_DIR}"
        RESULT_VARIABLE result OUTPUT_VARIABLE output ERROR_VARIABLE error)
    if(NOT result EQUAL 0)
        message(FATAL_ERROR "Cannot apply ABC allocation checks: ${output}${error}")
    endif()
endif()
