# AUTHORS: Dan Liew, Ryan Gvostes, Mate Soos
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

#AddGTestSuite(unit-tests)
# -----------------------------------------------------------------------------
# C API tests (these should be .cpp or .cxx files because GTest needs C++)
# -----------------------------------------------------------------------------
AddSTPGTest(PropagateEqualities_Test.cpp)
AddSTPGTest(SimplifyingNodeFactory_Test.cpp)
AddSTPGTest(FindPureLiterals_Test.cpp)
AddSTPGTest(Flatten_Test.cpp)
AddSTPGTest(NodeDomainAnalysis_Test.cpp)
AddSTPGTest(SplitExtracts_Test.cpp)
AddSTPGTest(StrengthReduction_Test.cpp)
AddSTPGTest(AlwaysTrue_Test.cpp)
AddSTPGTest(MergeSame_Test.cpp)

