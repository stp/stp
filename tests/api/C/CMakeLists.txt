# -----------------------------------------------------------------------------
# Find GTest library which will be used to drive tests
# -----------------------------------------------------------------------------
find_package(GTest REQUIRED)
include_directories(${GTEST_INCLUDE_DIRS})

add_custom_target(C-api-tests)
add_dependencies(check C-api-tests)

include(AddSTPGTest)

# -----------------------------------------------------------------------------
# Find the public headers associated with libstp
# -----------------------------------------------------------------------------
get_target_property(libstp_headers libstp PUBLIC_HEADER)
foreach(header ${libstp_headers})
    get_filename_component(headerDir ${header} DIRECTORY)
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
AddSTPGTest(C-api-tests parsefile-using-cinterface.cpp)
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
AddSTPGTest(C-api-tests stp-test3.cpp)
AddSTPGTest(C-api-tests timeout.cpp)
AddSTPGTest(C-api-tests x.cpp)
AddSTPGTest(C-api-tests y.cpp)
