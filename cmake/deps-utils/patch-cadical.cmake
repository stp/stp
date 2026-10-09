# ExternalProject can repeat its patch step when the command changes. An
# existing build may already carry the observation patch, so apply each
# patch only when its reverse does not match the checkout.
if(NOT EXISTS "${SOURCE_DIR}/src/cadical.hpp")
    message(FATAL_ERROR "SOURCE_DIR must name a CaDiCaL checkout")
endif()

# Git exports GIT_DIR, GIT_INDEX_FILE and their kind to what it runs (a hook,
# `git rebase -x`), naming the repository that runs it -- in a linked
# worktree, STP's own. Every git command below acts on the CaDiCaL checkout
# alone: these are cleared, and each command names the checkout with -C.
execute_process(
    COMMAND git rev-parse --local-env-vars
    OUTPUT_VARIABLE git_local_vars OUTPUT_STRIP_TRAILING_WHITESPACE ERROR_QUIET)
string(REPLACE "\n" ";" git_local_vars "${git_local_vars}")
foreach(var ${git_local_vars})
    unset(ENV{${var}})
endforeach()

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
# (Cadical::supportsDecisionPolarity), as it does --cadical-factor. So is
# clause import with post-load search diversification, which a forking
# client uses (Cadical::connectClauseExchange).
if(CADICAL_VERSION VERSION_GREATER_EQUAL "3.0.0")
    set(patches cadical-observe-witness-taint-restore.patch
                cadical-decision-polarity.patch
                cadical-clause-import.patch)
else()
    set(patches cadical-observe-witness-taint-restore-2.x.patch)
endif()

# The patch set an earlier patch step left in this checkout (FindCaDiCaL's
# CADICAL_PATCH_SET). When it is another set, or none was recorded, the
# checkout goes back to its tag first: a changed patch applies to neither the
# old patched sources nor their reverse.
set(stamp "${SOURCE_DIR}/.stp-patch-set")
set(recorded "")
if(EXISTS "${stamp}")
    file(READ "${stamp}" recorded)
    string(STRIP "${recorded}" recorded)
endif()
if(DEFINED STP_PATCH_SET AND NOT recorded STREQUAL STP_PATCH_SET)
    execute_process(
        COMMAND git -C "${SOURCE_DIR}" checkout -f -- .
        WORKING_DIRECTORY "${SOURCE_DIR}"
        RESULT_VARIABLE restored OUTPUT_QUIET ERROR_VARIABLE error)
    if(restored EQUAL 0)
        execute_process(
            COMMAND git -C "${SOURCE_DIR}" clean -fd
            WORKING_DIRECTORY "${SOURCE_DIR}"
            RESULT_VARIABLE restored OUTPUT_QUIET ERROR_VARIABLE error)
    endif()
    if(NOT restored EQUAL 0)
        message(FATAL_ERROR "Cannot restore the CaDiCaL checkout before patching: ${error}")
    endif()
    if(NOT recorded STREQUAL "")
        message(STATUS "CaDiCaL checkout carried another patch set: restored")
    endif()
endif()

foreach(patch ${patches})
    set(path "${CMAKE_CURRENT_LIST_DIR}/${patch}")
    execute_process(
        COMMAND git -C "${SOURCE_DIR}" apply --unidiff-zero --reverse --check "${path}"
        WORKING_DIRECTORY "${SOURCE_DIR}"
        RESULT_VARIABLE already_applied OUTPUT_QUIET ERROR_QUIET)
    if(already_applied EQUAL 0)
        message(STATUS "CaDiCaL patch already applied: ${patch}")
    else()
        execute_process(
            COMMAND git -C "${SOURCE_DIR}" apply --unidiff-zero "${path}"
            WORKING_DIRECTORY "${SOURCE_DIR}"
            RESULT_VARIABLE result OUTPUT_VARIABLE output ERROR_VARIABLE error)
        if(NOT result EQUAL 0)
            message(FATAL_ERROR "Cannot apply CaDiCaL patch ${patch}: ${output}${error}")
        endif()
    endif()
endforeach()

configure_file("${CMAKE_CURRENT_LIST_DIR}/cadical-CMakeLists.txt"
               "${SOURCE_DIR}/CMakeLists.txt" COPYONLY)
if(DEFINED STP_PATCH_SET)
    file(WRITE "${stamp}" "${STP_PATCH_SET}\n")
endif()
