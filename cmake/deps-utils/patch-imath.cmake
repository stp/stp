# ExternalProject can repeat its patch step when the command changes, and a
# moved STP_DEP_DIR is enough to do it: <INSTALL_DIR> is part of the step's
# arguments. The checkout it re-runs on already carries the patch, so apply it
# only when its reverse does not match, as deps-utils/patch-cadical.cmake and
# deps-utils/patch-highs.cmake already do for theirs.
if(NOT EXISTS "${SOURCE_DIR}/imath.h")
    message(FATAL_ERROR "SOURCE_DIR must name an IMath checkout")
endif()

# --unidiff-zero on both calls: the patch is regenerated with zero context so
# that `git diff --check` accepts it, and the reverse check has to read it the
# same way the forward application does.
set(patch "${CMAKE_CURRENT_LIST_DIR}/imath-no-gmp-names-immutable-tuning.patch")
execute_process(
    COMMAND git apply --unidiff-zero --reverse --check "${patch}"
    WORKING_DIRECTORY "${SOURCE_DIR}"
    RESULT_VARIABLE already_applied OUTPUT_QUIET ERROR_QUIET)
if(already_applied EQUAL 0)
    message(STATUS "IMath patch already applied")
else()
    execute_process(
        COMMAND git apply --unidiff-zero "${patch}"
        WORKING_DIRECTORY "${SOURCE_DIR}"
        RESULT_VARIABLE result OUTPUT_VARIABLE output ERROR_VARIABLE error)
    if(NOT result EQUAL 0)
        message(FATAL_ERROR "Cannot apply IMath patch: ${output}${error}")
    endif()
endif()

# Upstream carries no CMakeLists, so supply the one that builds the two files
# STP needs. Copied here rather than in a second patch step, so that the whole
# step is this one script and repeating it is safe.
configure_file("${CMAKE_CURRENT_LIST_DIR}/imath-CMakeLists.txt"
               "${SOURCE_DIR}/CMakeLists.txt" COPYONLY)
