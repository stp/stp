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

    # The same allocator the stp binary links, for the same reason: the unit
    # tests are as allocation-heavy as a solve -- the exhaustive ones build and
    # tear down millions of interned nodes -- and on those the C library
    # allocator is a fifth of the run. Listing it first keeps its definitions
    # ahead of libc. Not under valgrind: memcheck replaces malloc by preloading
    # into the process, and an allocator linked into the executable takes those
    # calls before the preload sees them, so the run would report nothing.
    # (-DSTP_ALLOCATOR=system opts out, which is what a sanitizer build already
    # does.)
    set(test_allocator "")
    if(NOT USE_VALGRIND)
        set(test_allocator ${STP_ALLOCATOR_LIBRARY})
    endif()

    # Several unit tests include stp/Sat/Cadical.h directly (each guarded by
    # #ifdef USE_CADICAL), which pulls in CaDiCaL's own header; and a shared
    # libstp localises the symbols it took from libcadical.a (--exclude-libs),
    # so a test that reaches CaDiCaL needs its own copy -- the same arrangement
    # as the $<TARGET_FILE:libabc-pic> on the tests that instantiate
    # BBNodeManagerAIG. Given to every unit test rather than tracked per file:
    # this is what the project-wide link_libraries() it replaces already did,
    # an archive contributes nothing to a test that does not reference it, and
    # a list kept by hand would rot the first time a test grew the include.
    set(test_cadical "")
    if(USE_CADICAL)
        set(test_cadical CaDiCaL)
    endif()

    target_link_libraries(${testname}
        ${test_allocator} stp ${GTEST_BOTH_LIBRARIES} ${test_cadical}
    )

    # Add dependency so that building the testsuite
    # will cause this test (testname) to be built
    #add_dependencies(${TESTSUITE} ${testname})
    if(USE_VALGRIND)
        add_test(
          NAME ${testname}-gtest
          COMMAND ${VALGRIND_TOOL} ${VALGRIND_ARGS} $<TARGET_FILE:${testname}>
          WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
        )
        # Valgrind costs roughly an order of magnitude in run time, which the
        # exhaustive tests in particular do not fit into the default timeout.
        set_tests_properties(${testname}-gtest PROPERTIES TIMEOUT ${VALGRIND_TEST_TIMEOUT})
    else()
        add_test(
          NAME ${testname}-gtest
          COMMAND ${testname}
          WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
        )
    endif()
endfunction()
