# AUTHORS: Dan Liew, Ryan Govostes, Mate Soos, Andrew Teylu
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

# -----------------------------------------------------------------------------
# Tests of libstp2, the 2.x C API (c_interface.h) re-implemented over the 3.x C
# API: a few of the 2.x suites, unchanged, covering the handle lifecycle,
# counterexamples, push and pop, parsing, Expr ownership, the counter enum's
# ABI, floating point and the header-only fp.hpp over it, uninterpreted
# functions, arrays and the reason a query had no answer. Every 2.x suite,
# these included, is also rewritten against the 3.x API in tests/api/cpp3.
# (These are .cpp files because GTest needs C++.)
# -----------------------------------------------------------------------------
AddSTPGTest(interface-check.cpp)
target_link_libraries(interface-checkTests stp2)
AddSTPGTest(stp-counterex.cpp)
target_link_libraries(stp-counterexTests stp2)
AddSTPGTest(push-pop.cpp)
target_link_libraries(push-popTests stp2)
AddSTPGTest(parsestring-using-cinterface.cpp)
target_link_libraries(parsestring-using-cinterfaceTests stp2)
AddSTPGTest(persist-delete.cpp)
target_link_libraries(persist-deleteTests stp2)
AddSTPGTest(counter-enum-abi.cpp)
target_link_libraries(counter-enum-abiTests stp2)
AddSTPGTest(fp-arithmetic.cpp)
target_link_libraries(fp-arithmeticTests stp2)
AddSTPGTest(fp-cpp-wrapper.cpp)
target_link_libraries(fp-cpp-wrapperTests stp2)
AddSTPGTest(uninterpreted-functions-api.cpp)
target_link_libraries(uninterpreted-functions-apiTests stp2)
AddSTPGTest(stp-array-model.cpp)
target_link_libraries(stp-array-modelTests stp2)
AddSTPGTest(reason-unknown.cpp)
target_link_libraries(reason-unknownTests stp2)
