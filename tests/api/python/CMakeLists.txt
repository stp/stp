set(PYTHON_INTERFACE_DIR ${CMAKE_BINARY_DIR}/bindings/python)
configure_file(tests.py.in tests.py @ONLY)

add_custom_target(python-interface-tests
                  DEPENDS libstp
                  COMMAND ${PYTHON_EXECUTABLE}
                          ${CMAKE_CURRENT_BINARY_DIR}/tests.py
                  COMMENT "Running Python interface tests"
                 )

# Make sure this test-suite runs when "check" is target
add_dependencies(check python-interface-tests)
