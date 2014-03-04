# -----------------------------------------------------------------------------
# Find GTest library which will be used to drive tests
# -----------------------------------------------------------------------------
# GoogleTest devs don't recommend using a pre-built GTest library
# ( https://code.google.com/p/googletest/wiki/FAQ#Why_is_it_not_recommended_to_install_a_pre-compiled_copy_of_Goog ).
# Because of this, distros like Ubuntu don't provide a pre-built GTest library
# so ``find_package(GTest REQUIRED)`` fails.
#
# Instead it is recommended that projects build their own copy of GTest. Detecting
# the location of GTest source code is probably error prone so using a copy in the 
# repository seems like the easiest thing to do. This also has the added benefit that
# everyone uses the same version of GTest.
set(GTEST_PREFIX ${CMAKE_SOURCE_DIR}/utils/gtest)
add_subdirectory(${GTEST_PREFIX} gtest)
set(GTEST_BOTH_LIBRARIES gtest gtest_main)

include_directories(${GTEST_PREFIX}/include)
add_custom_target(C-api-tests)
add_dependencies(check C-api-tests)

include(AddSTPGTest)

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
