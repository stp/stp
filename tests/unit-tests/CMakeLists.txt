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

#AddGTestSuite(unit-tests)
# -----------------------------------------------------------------------------
# C API tests (these should be .cpp or .cxx files because GTest needs C++)
# -----------------------------------------------------------------------------
AddSTPGTest(LazyWriteChainReads_Test.cpp)
AddSTPGTest(IncrementalCBP_Test.cpp)
AddSTPGTest(IncrementalEncodingEpoch_Test.cpp)
AddSTPGTest(IncrementalLifetimeState_Test.cpp)
AddSTPGTest(IncrementalPolicy_Test.cpp)
AddSTPGTest(IncrementalScopeState_Test.cpp)
AddSTPGTest(IncrementalActiveReads_Test.cpp)
AddSTPGTest(ArrayTransformerRegistry_Test.cpp)
AddSTPGTest(ArrayReadRefinementProgress_Test.cpp)
AddSTPGTest(SATSolver_Test.cpp)
AddSTPGTest(SatSolverBudget_Test.cpp)
AddSTPGTest(TrailReuse_Test.cpp)
AddSTPGTest(SuggestPhase_Test.cpp)
AddSTPGTest(UnsatAssumptions_Test.cpp)
AddSTPGTest(PropagateEqualities_Test.cpp)
AddSTPGTest(SimplifyingNodeFactory_Test.cpp)
AddSTPGTest(SelfStoreEquality_Test.cpp)
AddSTPGTest(FindPureLiterals_Test.cpp)
AddSTPGTest(Flatten_Test.cpp)
AddSTPGTest(FlattenKindSharing_Test.cpp)
AddSTPGTest(CommonSubSum_Test.cpp)
AddSTPGTest(UserDefinedFlags_Test.cpp)
AddSTPGTest(NarrowWidenedFPComparison_Test.cpp)
AddSTPGTest(NarrowWidenedFPEquality_Test.cpp)
AddSTPGTest(NodeDomainAnalysis_Test.cpp)
AddSTPGTest(SplitExtracts_Test.cpp)
AddSTPGTest(SourceSortMemo_Test.cpp)
# The AIG gate builders, which every build has. Instantiating
# BBNodeManagerAIG calls ABC through its inline members, and a shared libstp
# localises ABC's symbols (--exclude-libs), so this links its own copy the
# way FloatBlast_Test does below.
AddSTPGTest(BBNodeManagerAIG_Test.cpp)
target_link_libraries(BBNodeManagerAIG_TestTests $<TARGET_FILE:libabc-pic>)
add_dependencies(BBNodeManagerAIG_TestTests libabc-pic)
AddSTPGTest(FPPrintBack_Test.cpp)
AddSTPGTest(FloatBlast_Test.cpp)
# The native-comparison differential instantiates BBNodeManagerAIG, whose
# inline members call ABC. A shared libstp localises ABC's symbols
# (--exclude-libs), so this test links its own copy; the AIG package keeps
# all of its state in the manager struct, which is shared fine. Linking
# the archive by file keeps ABC's interface flags (-fno-exceptions) off
# the test's own compilation.
target_link_libraries(FloatBlast_TestTests $<TARGET_FILE:libabc-pic>)
add_dependencies(FloatBlast_TestTests libabc-pic)
AddSTPGTest(FpTotalise_Test.cpp)
# Truth values the model-formula evaluator gives the two float
# equalities; the circuit's answers are covered elsewhere.
AddSTPGTest(FpModelEquality_Test.cpp)
AddSTPGTest(SourceSort_Test.cpp)
# Builds float/rounding-mode constants, which is the whole point.
AddSTPGTest(ConstantIdentity_Test.cpp)
AddSTPGTest(FpConstantFold_Test.cpp)
# The LibBF-backed real-literal conversion.
AddSTPGTest(DecimalToFP_Test.cpp)
# The oracle is the hardware, evaluated under a rounding mode set with
# fesetround. Without this the compiler assumes the default mode and
# folds the reference arithmetic while compiling, so every non-default
# mode disagrees for a reason that has nothing to do with STP.
if (TARGET FpConstantFold_TestTests AND NOT MSVC)
    target_compile_options(FpConstantFold_TestTests PRIVATE -frounding-math)
    # And on 32-bit x86 the default is x87, which keeps a 64-bit
    # significand and so double-rounds on the way to binary64: the
    # hardware then disagrees with a correctly-rounded result, e.g.
    # 3.0 / 1.0000000000000002 under RNE. binary32 has guard bits to
    # spare, which is why only the binary64 tests would notice. SSE2
    # arithmetic is correctly rounded, so ask for it and the oracle is
    # IEEE again rather than skipping the coverage.
    if (CMAKE_SIZEOF_VOID_P EQUAL 4)
        include(CheckCXXCompilerFlag)
        check_cxx_compiler_flag("-msse2 -mfpmath=sse" HAVE_SSE_MATH_FLAGS)
        if (HAVE_SSE_MATH_FLAGS)
            target_compile_options(FpConstantFold_TestTests
                                   PRIVATE -msse2 -mfpmath=sse)
        endif()
    endif()
endif()
AddSTPGTest(BVSolver_Test.cpp)
AddSTPGTest(NaryBvmult_Test.cpp)
AddSTPGTest(StrengthReduction_Test.cpp)
# Bit-blasts each operation to check the difficulty score against what the
# AIG really costs, so it instantiates BBNodeManagerAIG and needs its own
# copy of ABC for the same reason FloatBlast_Test does.
AddSTPGTest(DifficultyScore_Test.cpp)
target_link_libraries(DifficultyScore_TestTests $<TARGET_FILE:libabc-pic>)
add_dependencies(DifficultyScore_TestTests libabc-pic)
AddSTPGTest(StrengthReduction_Exhaustive_Test.cpp)
AddSTPGTest(RemoveUnconstrained_Exhaustive_Test.cpp)
AddSTPGTest(RemoveUnconstrainedFpDiv_Test.cpp)
AddSTPGTest(AchievableImage_Exhaustive_Test.cpp)
AddSTPGTest(Rewriting_Exhaustive_Test.cpp)
AddSTPGTest(SimplifyFormula_Test.cpp)
AddSTPGTest(SimplifyingNodeFactory_Exhaustive_Test.cpp)
AddSTPGTest(ConstantEvaluator_Exhaustive_Test.cpp)
AddSTPGTest(DivModPow2_Test.cpp)
AddSTPGTest(UnsignedIntervalPropagators_Test.cpp)
AddSTPGTest(UnsignedIntervalExhaustive_Test.cpp)
AddSTPGTest(UnsignedIntervalWide_Test.cpp)
AddSTPGTest(MergeSame_Test.cpp)
AddSTPGTest(ConstantBitP_TransferFunctions_Test.cpp)
AddSTPGTest(ConstantBitP_Wide_Test.cpp)
AddSTPGTest(UnsignedIntervalAnalysis_Test.cpp)
AddSTPGTest(ConstantBitPropagation_Test.cpp)
AddSTPGTest(Extensionality_Test.cpp)
AddSTPGTest(BitVector_from_Dec_Test.cpp)
AddSTPGTest(ValueSet_Test.cpp)
AddSTPGTest(ValueSet_Exhaustive_Test.cpp)
AddSTPGTest(SearchBias_Test.cpp)
AddSTPGTest(Bva_Test.cpp)
AddSTPGTest(IncrementalEngagement_Test.cpp)
AddSTPGTest(SATSolverConfigWindow_Test.cpp)
AddSTPGTest(FdOStream_Test.cpp)
# Deeply nested input must not put the AST-depth-recursive traversals through
# the call stack. Each case runs in a forked child on a 1 MiB stack.
AddSTPGTest(DeepDag_Test.cpp)
# Instantiates BBNodeManagerAIG, whose inline members call ABC; a shared
# libstp localises ABC's symbols, so this links its own copy the way
# FloatBlast_Test does.
target_link_libraries(DeepDag_TestTests $<TARGET_FILE:libabc-pic>)
add_dependencies(DeepDag_TestTests libabc-pic)
# The check that a primed pass still walks what its priming visits. Debug-only,
# like the audit it drives: under NDEBUG the cases compile away and the binary
# reports nothing to run.
AddSTPGTest(PrimeMemo_Test.cpp)
