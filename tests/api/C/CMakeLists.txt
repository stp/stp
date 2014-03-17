# -----------------------------------------------------------------------------
# Setup custom target
# -----------------------------------------------------------------------------
set(TESTSUITE "C-api-tests") # Unit test group name
add_custom_target(${TESTSUITE})
add_dependencies(check ${TESTSUITE})

add_custom_command(TARGET ${TESTSUITE}
                   POST_BUILD
                   COMMAND ${LIT_TOOL} -s -v ${CMAKE_CURRENT_BINARY_DIR}
                   COMMENT "Running ${TESTSUITE}"
                  )

# -----------------------------------------------------------------------------
# Setup lit configuration
# -----------------------------------------------------------------------------
configure_file(${CMAKE_SOURCE_DIR}/tests/lit-unit-tests-common.site.cfg.in
               ${CMAKE_CURRENT_BINARY_DIR}/lit.site.cfg
               @ONLY@
              )
# -----------------------------------------------------------------------------
# Find the public headers associated with libstp
# -----------------------------------------------------------------------------
get_target_property(libstp_headers libstp PUBLIC_HEADER)
foreach(header ${libstp_headers})
    get_filename_component(headerDir ${header} PATH) # FIXME: CMake >=2.8.12 has DIRECTORY instead of PATH which is easier to understand
    include_directories(${headerDir})
endforeach()

# -----------------------------------------------------------------------------
# C API tests (these should be .cpp or .cxx files because GTest needs C++)
# -----------------------------------------------------------------------------
AddSTPGTest(${TESTSUITE} array-cvcl-02.cpp)
AddSTPGTest(${TESTSUITE} b4-c2.cpp)
AddSTPGTest(${TESTSUITE} b4-c.cpp)
AddSTPGTest(${TESTSUITE} getbvunsignedlonglong-check.cpp)
AddSTPGTest(${TESTSUITE} if-check.cpp)
AddSTPGTest(${TESTSUITE} interface-check.cpp)
AddSTPGTest(${TESTSUITE} multiple-queries.cpp)
AddSTPGTest(${TESTSUITE} parsefile-using-cinterface.cpp
                        CVC_FILE=\"${CMAKE_CURRENT_SOURCE_DIR}/t.cvc\"
           )
AddSTPGTest(${TESTSUITE} parsestring-using-cinterface.cpp)
AddSTPGTest(${TESTSUITE} print.cpp)
AddSTPGTest(${TESTSUITE} push-no-pop.cpp)
AddSTPGTest(${TESTSUITE} push-pop.cpp)
AddSTPGTest(${TESTSUITE} sbvdiv.cpp)
AddSTPGTest(${TESTSUITE} simplify.cpp)
AddSTPGTest(${TESTSUITE} stp-array-model.cpp)
AddSTPGTest(${TESTSUITE} stp-bool.cpp)
AddSTPGTest(${TESTSUITE} stpcheck.cpp)
AddSTPGTest(${TESTSUITE} stp-counterex.cpp)
AddSTPGTest(${TESTSUITE} stp-div-001.cpp)
AddSTPGTest(${TESTSUITE} stp-test3.cpp
                        CVC_FILE=\"${CMAKE_CURRENT_SOURCE_DIR}/f.cvc\"
           )
AddSTPGTest(${TESTSUITE} timeout.cpp
                        SMT_FILE=\"${CMAKE_CURRENT_SOURCE_DIR}/example.smt\"
           )
AddSTPGTest(${TESTSUITE} x.cpp)
AddSTPGTest(${TESTSUITE} y.cpp)
