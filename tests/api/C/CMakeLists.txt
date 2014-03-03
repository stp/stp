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
#AddSTPGTest(C-api-tests array-cvcl-02.cpp)
