if (Boost_FOUND)
    get_target_property(STP_EXECUTABLE_PATH stp LOCATION)
else()
    get_target_property(STP_EXECUTABLE_PATH stp_simple LOCATION)
endif()

# Create llvm-lit configuration file
configure_file(lit.site.cfg.in lit.site.cfg @ONLY)

if (Boost_FOUND)
    add_custom_target(query-file-tests
                  DEPENDS stp
                  COMMAND ${LIT_TOOL} ${LIT_ARGS} .
    )
else()
    add_custom_target(query-file-tests
                  DEPENDS stp_simple
                  COMMAND ${LIT_TOOL} ${LIT_ARGS} .
    )
endif()

# Make sure this test-suite runs when "check" is target
add_dependencies(check query-file-tests)