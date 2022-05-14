# Sets for the current directory (and below) the testsuite to use.
# This macro should be used with the AddSTPGTest function.
macro(AddGTestSuite TESTSUITENAME)
    # Setup lit configuration
    configure_file(${CMAKE_SOURCE_DIR}/tests/lit-unit-tests-common.site.cfg.in
                   ${CMAKE_CURRENT_BINARY_DIR}/lit.site.cfg
                   @ONLY
                  )

    if(USE_VALGRIND)
        set(LIT_EXTRA_FLAGS --vg --vg-leak)
    else()
        set(LIT_EXTRA_FLAGS "")
    endif()

    add_test (
        NAME ${TESTSUITENAME}-gtest-suite
        COMMAND ${LIT_TOOL} ${LIT_ARGS} ${LIT_EXTRA_FLAGS} ${CMAKE_CURRENT_BINARY_DIR}
        WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
    )
endmacro()
