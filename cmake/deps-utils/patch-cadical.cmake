# ExternalProject can repeat its patch step when the command changes. An
# existing build may already carry the observation patch, so apply each
# patch only when its reverse does not match the checkout.
if(NOT EXISTS "${SOURCE_DIR}/src/cadical.hpp")
    message(FATAL_ERROR "SOURCE_DIR must name a CaDiCaL checkout")
endif()

# CADICAL_VERSION comes from cmake/FindCaDiCaL.cmake, which decides
# CADICAL_HAS_DECISION_POLARITY from the same value, so the patches applied
# here and the feature the build compiles in cannot disagree. Run by hand,
# the checkout's own VERSION file says which line it is.
if(NOT DEFINED CADICAL_VERSION OR CADICAL_VERSION STREQUAL "")
    file(STRINGS "${SOURCE_DIR}/VERSION" CADICAL_VERSION LIMIT_COUNT 1)
endif()

# Both patches are written against the 3.x sources. The witness fix is a
# correctness fix, so the 2.x line gets its own port of it: there the same
# spot is an assert(false) that a release build of CaDiCaL compiles out.
# Decision-time polarity advice is an optional capability: a 2.x CaDiCaL is
# built without it and reports it unsupported
# (Cadical::supportsDecisionPolarity), as it does --cadical-factor.
if(CADICAL_VERSION VERSION_GREATER_EQUAL "3.0.0")
    set(patches cadical-observe-witness-taint-restore.patch
                cadical-decision-polarity.patch)
else()
    set(patches cadical-observe-witness-taint-restore-2.x.patch)
endif()

foreach(patch ${patches})
    set(path "${CMAKE_CURRENT_LIST_DIR}/${patch}")
    execute_process(
        COMMAND git apply --unidiff-zero --reverse --check "${path}"
        WORKING_DIRECTORY "${SOURCE_DIR}"
        RESULT_VARIABLE already_applied OUTPUT_QUIET ERROR_QUIET)
    if(already_applied EQUAL 0)
        message(STATUS "CaDiCaL patch already applied: ${patch}")
    else()
        execute_process(
            COMMAND git apply --unidiff-zero "${path}"
            WORKING_DIRECTORY "${SOURCE_DIR}"
            RESULT_VARIABLE result OUTPUT_VARIABLE output ERROR_VARIABLE error)
        if(NOT result EQUAL 0)
            message(FATAL_ERROR "Cannot apply CaDiCaL patch ${patch}: ${output}${error}")
        endif()
    endif()
endforeach()

configure_file("${CMAKE_CURRENT_LIST_DIR}/cadical-CMakeLists.txt"
               "${SOURCE_DIR}/CMakeLists.txt" COPYONLY)
