AddGTestSuite(C-api-tests)
# -----------------------------------------------------------------------------
# C API tests (these should be .cpp or .cxx files because GTest needs C++)
# -----------------------------------------------------------------------------
AddSTPGTest(array-cvcl-02.cpp)
AddSTPGTest(array-ite.cpp)
AddSTPGTest(b4-c2.cpp)
AddSTPGTest(b4-c.cpp)
AddSTPGTest(getbv.cpp)
AddSTPGTest(if-check.cpp)
AddSTPGTest(interface-check.cpp)
AddSTPGTest(leaks.cpp)
AddSTPGTest(multiple-queries.cpp)
AddSTPGTest(parsefile-using-cinterface.cpp
                        CVC_FILE=\"${CMAKE_CURRENT_SOURCE_DIR}/t.cvc\"
           )
AddSTPGTest(parsestring-using-cinterface.cpp)
AddSTPGTest(print.cpp)
AddSTPGTest(push-no-pop.cpp)
AddSTPGTest(push-pop.cpp)
AddSTPGTest(sbvdiv.cpp)
AddSTPGTest(simplify.cpp)
AddSTPGTest(stp-array-model.cpp)
AddSTPGTest(stp-bool.cpp)
AddSTPGTest(stpcheck.cpp)
AddSTPGTest(stp-counterex.cpp)
AddSTPGTest(stp-div-001.cpp)
AddSTPGTest(stp-test3.cpp
                        CVC_FILE=\"${CMAKE_CURRENT_SOURCE_DIR}/f.cvc\"
           )
AddSTPGTest(timeout.cpp
                        SMT_FILE=\"${CMAKE_CURRENT_SOURCE_DIR}/example.smt\"
           )
AddSTPGTest(x.cpp)
AddSTPGTest(y.cpp)
AddSTPGTest(multi-query-bug.cpp)
AddSTPGTest(reported_error.cpp)
