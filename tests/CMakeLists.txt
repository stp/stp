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
       OFF
      )

if(TEST_APIS)
    message(FATAL_ERROR "TODD")
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
    message(FATAL_ERROR "TODD")
    add_subdirectory(generated-tests)
endif()
