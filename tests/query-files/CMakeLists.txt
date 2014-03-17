get_target_property(STP_EXECUTABLE_PATH stp LOCATION)

# Create llvm-lit configuration file
configure_file(lit.site.cfg.in lit.site.cfg @ONLY)

add_custom_target(query-file-tests
                  DEPENDS stp
                  COMMAND ${PYTHON_EXECUTABLE} 
                          ${LIT_TOOL} -v -s . 
                 )

# Make sure this test-suite runs when "check" is target
add_dependencies(check query-file-tests)
