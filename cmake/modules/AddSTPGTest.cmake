# AUTHORS: Dan Liew, Ryan Govostes, Mate Soos
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
# THE SOFTWARE.

# AddSTPGTest(<sourcefile> [<defines> ...])
#
# Adds a GoogleTest to the current test suite (${TESTSUITE})
# with executable name <sourcefile> with the file extension removed and
# the UNIT_TEST_EXE_SUFFIX appended.
# The executable will be linked with libstp.
# Remaining arguments to this function are interpreted as preprocessor macros
# to defines.
#
# e.g.
# AddSTPGTest(mysimpleprogram.cpp FOO=15 BAR=\"a string\")
#
function(AddSTPGTest sourcefile)
    get_filename_component(testname ${sourcefile} NAME_WE)

    # testname has suffix because lit expects this
    set(testname "${testname}${UNIT_TEST_EXE_SUFFIX}")

    add_executable(${testname} ${sourcefile})

    # Add define flags requested by users
    list(LENGTH ARGN LEN_ARGN)
    if(LEN_ARGN GREATER 0)
        set_property(TARGET ${testname} APPEND PROPERTY COMPILE_DEFINITIONS ${ARGN})
        #message(STATUS "Added flags to test ${testname} ${ARGN}")
    endif()

    target_link_libraries(${testname}
        stp ${GTEST_BOTH_LIBRARIES}
    )

    # Add dependency so that building the testsuite
    # will cause this test (testname) to be built
    #add_dependencies(${TESTSUITE} ${testname})
    add_test(
      NAME ${testname}-gtest
      COMMAND ${testname}
      WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
    )
endfunction()
