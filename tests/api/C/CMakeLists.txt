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

#AddGTestSuite(C-api-tests)
# -----------------------------------------------------------------------------
# C API tests (these should be .cpp or .cxx files because GTest needs C++)
# -----------------------------------------------------------------------------
AddSTPGTest(array-cvcl-02.cpp)
AddSTPGTest(array-equality-retired-after-pop.cpp)
AddSTPGTest(bv-abstraction-array-candidate-is-bound.cpp)
AddSTPGTest(array-extensionality.cpp)
AddSTPGTest(array-ite.cpp)
AddSTPGTest(b4-c2.cpp)
AddSTPGTest(b4-c.cpp)
AddSTPGTest(bvconst-width.cpp)
AddSTPGTest(getbv.cpp)
AddSTPGTest(hoangmle.cpp)
AddSTPGTest(if-check.cpp)
AddSTPGTest(incremental-auto-engage.cpp)
AddSTPGTest(interface-check.cpp)
AddSTPGTest(leaks.cpp)
AddSTPGTest(multiple-queries.cpp)
AddSTPGTest(parsefile-using-cinterface.cpp
                        CVC_FILE=\"${CMAKE_CURRENT_SOURCE_DIR}/t.cvc\"
           )
AddSTPGTest(parsestring-using-cinterface.cpp)
AddSTPGTest(print.cpp)
AddSTPGTest(multi-print.cpp)
AddSTPGTest(push-no-pop.cpp)
AddSTPGTest(push-pop.cpp)
AddSTPGTest(push-pop-model.cpp)
AddSTPGTest(reason-unknown.cpp)
AddSTPGTest(refinement-flags.cpp)
AddSTPGTest(incremental-query.cpp)
AddSTPGTest(sbvdiv.cpp)
AddSTPGTest(simplify.cpp)
AddSTPGTest(stp-array-model.cpp)
AddSTPGTest(stp-bool.cpp)
AddSTPGTest(stpcheck.cpp)
AddSTPGTest(stp-counterex.cpp)
AddSTPGTest(stp-div-001.cpp)
AddSTPGTest(stp-test3.cpp
                        CVC_FILE=\"${CMAKE_CURRENT_SOURCE_DIR}/f.cvc\"
           )
# AddSTPGTest(timeout.cpp
#                         SMT_FILE=\"${CMAKE_CURRENT_SOURCE_DIR}/example.smt\"
#            )
AddSTPGTest(x.cpp)
AddSTPGTest(y.cpp)
AddSTPGTest(multi-query-bug.cpp)
AddSTPGTest(reported_error.cpp)
AddSTPGTest(stp-even-eqn-assert.cpp)
AddSTPGTest(mdempsky.cpp)
AddSTPGTest(counterexample.cpp)
AddSTPGTest(example_broken.cpp)
AddSTPGTest(counter-example-reading.cpp)
AddSTPGTest(failing_solvermap.cpp)
AddSTPGTest(bit_string.cpp)
AddSTPGTest(check_sizes.cpp)
AddSTPGTest(timeout-budget.cpp)
AddSTPGTest(fp-model-reading.cpp)
AddSTPGTest(fp-model-roundtrip.cpp)
AddSTPGTest(fp-repeated-solve.cpp)
AddSTPGTest(fp-shared-bv-operand.cpp)
AddSTPGTest(fp-identity-passthrough.cpp)
AddSTPGTest(fp-lowered-ite-fold.cpp)
AddSTPGTest(fp-arithmetic.cpp)
AddSTPGTest(fp-constants-conversions.cpp)
AddSTPGTest(fp-multi-checker.cpp)
AddSTPGTest(fp-cpp-wrapper.cpp)
AddSTPGTest(fp-to-ieee-bv.cpp)
AddSTPGTest(fp-roundingmode-var.cpp)
AddSTPGTest(fp-roundingmode-survives-push-pop.cpp)
AddSTPGTest(fp-roundingmode-model-completion.cpp)
AddSTPGTest(fp-smt-equality.cpp)
AddSTPGTest(fp-arrays.cpp)
AddSTPGTest(fp-array-extensionality.cpp)
AddSTPGTest(fp-model-eval-predicates.cpp)
AddSTPGTest(fp-model-no-fp-in-query.cpp)
AddSTPGTest(model-read-with-no-solve.cpp)
AddSTPGTest(fp-printing.cpp)
AddSTPGTest(cadical.cpp)
AddSTPGTest(new-expr-kinds.cpp)
AddSTPGTest(varexpr-widths.cpp)
AddSTPGTest(uninterpreted-functions-api.cpp)
AddSTPGTest(uninterpreted-functions-handle-safety.cpp)
