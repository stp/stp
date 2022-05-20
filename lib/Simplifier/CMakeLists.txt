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

add_library(simplifier OBJECT
    BVSolver.cpp
    consteval.cpp
    PropagateEqualities.cpp
    RemoveUnconstrained.cpp
    Simplifier.cpp
    SubstitutionMap.cpp
    VariablesInExpression.cpp
    DifficultyScore.cpp
    UseITEContext.cpp
    FindPureLiterals.cpp
    StrengthReduction.cpp
    AIGSimplifyPropositionalCore.cpp
    UnsignedIntervalAnalysis.cpp
    Flatten.cpp
    NodeDomainAnalysis.cpp
    SplitExtracts.cpp

    constantBitP/ConstantBitP_Arithmetic.cpp
    constantBitP/ConstantBitP_Boolean.cpp
    constantBitP/ConstantBitP_Comparison.cpp
    constantBitP/ConstantBitP_Division.cpp
    constantBitP/ConstantBitP_MaxPrecision.cpp
    constantBitP/ConstantBitP_Multiplication.cpp
    constantBitP/ConstantBitPropagation.cpp
    constantBitP/ConstantBitP_Shifting.cpp
    constantBitP/ConstantBitP_TransferFunctions.cpp
    constantBitP/ConstantBitP_Utility.cpp
    constantBitP/FixedBits.cpp
)
add_dependencies(simplifier ASTKind_header)
if (NOT MSVC)
    set_source_files_properties(constantBitP/ConstantBitP_Division.cpp
        PROPERTIES COMPILE_FLAGS "-Wno-unreachable-code")
    set_source_files_properties(StrengthReduction.cpp
        PROPERTIES COMPILE_FLAGS "-Wno-unreachable-code")
endif()
