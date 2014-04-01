AddGTestSuite(C-api-tests)

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
AddSTPGTest(array-cvcl-02.cpp)
AddSTPGTest(array-ite.cpp)
AddSTPGTest(b4-c2.cpp)
AddSTPGTest(b4-c.cpp)
AddSTPGTest(getbvunsignedlonglong-check.cpp)
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
