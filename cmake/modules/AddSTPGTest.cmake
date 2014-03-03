# AddSTPGTest(<testsuite> <sourcefile>)
#
# Adds a GoogleTest to "testsuite" (just a custom target)
# with executable name "testname" that will link with libstp.
# Remaining arguments are the source files to build the test
function(AddSTPGTest testsuite sourcefile)
    get_filename_component(testname ${sourcefile} NAME_WE)
    add_executable(${testname} EXCLUDE_FROM_ALL ${sourcefile})
    target_link_libraries(${testname} libstp ${GTEST_BOTH_LIBRARIES})

    # Add dependency so that building the testsuite
    # will cause this test (testname) to be built
    add_dependencies(${testsuite} ${testname})

    add_test(${testname} ${testname})

    # Ensure that when using the run_ctest target this test gets built first
    add_dependencies(run_ctest ${testname})
endfunction()
