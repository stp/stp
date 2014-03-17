# -----------------------------------------------------------------------------
# Check we can find Python and the lit tool
# -----------------------------------------------------------------------------
find_package(PythonInterp REQUIRED)
mark_as_advanced(CLEAR PYTHON_EXECUTABLE) # Make visible in cmake-gui/ccmake

if(NOT PYTHONINTERP_FOUND)
    message(FATAL_ERROR "Python cannot be found. Please install it or disable testing.")
endif()

find_program(LIT_TOOL
             lit
             DOC "Path to lit tool"
            )

if(NOT LIT_TOOL)
    message(FATAL_ERROR "Could not find lit tool. Try setting LIT_TOOL to the full path for lit")
endif()

# Checking absolute path because if(EXISTS ...) behaviour only well
# defined if path is absolute
IF(NOT IS_ABSOLUTE "${LIT_TOOL}")
    message(FATAL_ERROR "LIT_TOOL must be set to an absolute PATH")
endif()

if(NOT EXISTS "${LIT_TOOL}")
    # Can happen if users environment changes after initial configure
    message(FATAL_ERROR "LIT_TOOL is set but the path does not seem to exist. Try deleting the LIT_TOOL cache variable and reconfiguring")
endif()

# -----------------------------------------------------------------------------
# Find GTest library which will be used to drive tests
# -----------------------------------------------------------------------------
# GoogleTest devs don't recommend using a pre-built GTest library
# ( https://code.google.com/p/googletest/wiki/FAQ#Why_is_it_not_recommended_to_install_a_pre-compiled_copy_of_Goog ).
# Because of this, distros like Ubuntu don't provide a pre-built GTest library
# so ``find_package(GTest REQUIRED)`` fails.
#
# Instead it is recommended that projects build their own copy of GTest. Detecting
# the location of GTest source code is probably error prone so using a copy in the 
# repository seems like the easiest thing to do. This also has the added benefit that
# everyone uses the same version of GTest.
set(GTEST_PREFIX ${CMAKE_SOURCE_DIR}/utils/gtest)
add_subdirectory(${GTEST_PREFIX} gtest)
set(GTEST_BOTH_LIBRARIES gtest gtest_main)

include_directories(${GTEST_PREFIX}/include)

include(AddSTPGTest)

# -----------------------------------------------------------------------------
# Tests that drive STP by using query files (e.g. smt2, smt and cvc files)
# -----------------------------------------------------------------------------

option(TEST_QUERY_FILES
       "Enable tests that use query files to drive STP" 
       ON
      )

if(TEST_QUERY_FILES)
    add_subdirectory(query-files)
endif()

# -----------------------------------------------------------------------------
# Tests that test STP's various different public APIs
# -----------------------------------------------------------------------------

# FIXME: Enable by default
option(TEST_APIS
       "Enable tests that test STP's public APIs" 
       ON
      )

if(TEST_APIS)
    add_subdirectory(api)
endif()

# -----------------------------------------------------------------------------
# Generated tests
# -----------------------------------------------------------------------------

# FIXME: Enable by default
option(TEST_GENERATED_QUERIES
       "Enable tests that are driven by automatically generated queries"
       OFF
      )

if(TEST_GENERATED_QUERIES)
    message(FATAL_ERROR "TODO")
    add_subdirectory(generated-tests)
endif()
