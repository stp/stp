#********************************************************************
# AUTHORS: Andrew Teylu
#
# BEGIN DATE: September, 2026
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
#********************************************************************
# -----------------------------------------------------------------------------
# Tests of the 3.x C API (<stp/stp.h>).
#
# smoke.c is compiled as C99: it proves the header is valid C and exercises
# every theory end to end. noexcept.cpp is a C++ consumer built without
# exceptions or RTTI. The gtest files walk the kind table, the parse/print
# round trips, the runtime rules (scopes, the failed state, lifetimes) and the
# interrupt from another thread.
# -----------------------------------------------------------------------------
add_executable(c-smoke smoke.c)
target_link_libraries(c-smoke stp)
if(NOT BUILD_SHARED_LIBS)
    # a static libstp needs the C++ runtime on the link line
    set_target_properties(c-smoke PROPERTIES LINKER_LANGUAGE CXX)
endif()
add_test(NAME c-smoke COMMAND c-smoke)

add_executable(c-noexcept noexcept.cpp)
target_link_libraries(c-noexcept stp)
if(NOT MSVC)
    target_compile_options(c-noexcept PRIVATE -fno-exceptions -fno-rtti)
endif()
add_test(NAME c-noexcept COMMAND c-noexcept)

# C handles released by a global object's destructor, at exit
add_executable(c-static-release static-release.cpp)
target_link_libraries(c-static-release stp)
add_test(NAME c-static-release COMMAND c-static-release)

AddSTPGTest(c-kinds.cpp)
AddSTPGTest(c-roundtrip.cpp)
AddSTPGTest(c-runtime.cpp)
AddSTPGTest(c-interrupt.cpp)
AddSTPGTest(c-const-arrays.cpp)
AddSTPGTest(c-runs.cpp)
find_package(Threads REQUIRED)
target_link_libraries(c-interrupt${UNIT_TEST_EXE_SUFFIX} Threads::Threads)

# Every test here carries the label api, as do those of tests/api/cpp and
# tests/api/python, so that ctest -L api runs the API's suites.
get_property(_api_tests DIRECTORY PROPERTY TESTS)
set_property(TEST ${_api_tests} APPEND PROPERTY LABELS api)

# The suites that run the library on several threads at once also carry the
# label threads, which the tsan job runs.
set_property(TEST c-interruptTests-gtest c-runtimeTests-gtest APPEND PROPERTY LABELS threads)
