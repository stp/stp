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
add_executable(c3-smoke smoke.c)
target_link_libraries(c3-smoke stp)
if(NOT BUILD_SHARED_LIBS)
    # a static libstp needs the C++ runtime on the link line
    set_target_properties(c3-smoke PROPERTIES LINKER_LANGUAGE CXX)
endif()
add_test(NAME c3-smoke COMMAND c3-smoke)

add_executable(c3-noexcept noexcept.cpp)
target_link_libraries(c3-noexcept stp)
if(NOT MSVC)
    target_compile_options(c3-noexcept PRIVATE -fno-exceptions -fno-rtti)
endif()
add_test(NAME c3-noexcept COMMAND c3-noexcept)

AddSTPGTest(c3-kinds.cpp)
AddSTPGTest(c3-roundtrip.cpp)
AddSTPGTest(c3-runtime.cpp)
AddSTPGTest(c3-interrupt.cpp)
AddSTPGTest(c3-const-arrays.cpp)
find_package(Threads REQUIRED)
target_link_libraries(c3-interrupt${UNIT_TEST_EXE_SUFFIX} Threads::Threads)
