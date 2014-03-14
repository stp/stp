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
AddSTPGTest(C-api-tests array-cvcl-02.cpp)
AddSTPGTest(C-api-tests b4-c2.cpp)
AddSTPGTest(C-api-tests b4-c.cpp)
AddSTPGTest(C-api-tests getbvunsignedlonglong-check.cpp)
AddSTPGTest(C-api-tests if-check.cpp)
AddSTPGTest(C-api-tests interface-check.cpp)
AddSTPGTest(C-api-tests multiple-queries.cpp)
AddSTPGTest(C-api-tests parsefile-using-cinterface.cpp
                        CVC_FILE=\"${CMAKE_CURRENT_SOURCE_DIR}/t.cvc\"
           )
AddSTPGTest(C-api-tests parsestring-using-cinterface.cpp)
AddSTPGTest(C-api-tests print.cpp)
AddSTPGTest(C-api-tests push-no-pop.cpp)
AddSTPGTest(C-api-tests push-pop.cpp)
AddSTPGTest(C-api-tests sbvdiv.cpp)
AddSTPGTest(C-api-tests simplify.cpp)
AddSTPGTest(C-api-tests stp-array-model.cpp)
AddSTPGTest(C-api-tests stp-bool.cpp)
AddSTPGTest(C-api-tests stpcheck.cpp)
AddSTPGTest(C-api-tests stp-counterex.cpp)
AddSTPGTest(C-api-tests stp-div-001.cpp)
AddSTPGTest(C-api-tests stp-test3.cpp
                        CVC_FILE=\"${CMAKE_CURRENT_SOURCE_DIR}/f.cvc\"
           )
AddSTPGTest(C-api-tests timeout.cpp
                        SMT_FILE=\"${CMAKE_CURRENT_SOURCE_DIR}/example.smt\"
           )
AddSTPGTest(C-api-tests x.cpp)
AddSTPGTest(C-api-tests y.cpp)
