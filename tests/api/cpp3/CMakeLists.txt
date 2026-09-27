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
# Tests of the 3.x C++ API (<stp/stp.hpp>). GTest files go through
# AddSTPGTest; smoke.cpp is a plain program with its own pass/fail exit code.
# -----------------------------------------------------------------------------
add_executable(api3-smoke smoke.cpp)
target_link_libraries(api3-smoke stp)
add_test(NAME api3-smoke COMMAND api3-smoke)

# The GoogleTest suites, one per area of the header. Every file includes
# api3_common.hpp from this directory.
AddSTPGTest(api3-kinds.cpp)
AddSTPGTest(api3-fp-to-real.cpp)
AddSTPGTest(api3-sorts.cpp)
AddSTPGTest(api3-values.cpp)
AddSTPGTest(api3-options.cpp)
AddSTPGTest(api3-solver.cpp)
AddSTPGTest(api3-solvers.cpp)
AddSTPGTest(api3-models.cpp)
AddSTPGTest(api3-parsing.cpp)
AddSTPGTest(api3-errors.cpp)
AddSTPGTest(api3-engine-failure.cpp)
AddSTPGTest(api3-rosetta.cpp)
AddSTPGTest(api3-const-arrays.cpp)
AddSTPGTest(api3-runs.cpp)

# The 2.x C API's suites, rewritten against this API: libstp carries no 2.x
# code, and tests/api/compat2 keeps a few of the originals to test libstp2. A
# suite that checks an internal property (a flag reaching the engine, what the
# extensionality checker holds) reaches the engine through api3_engine.hpp,
# which reads lib/Api/Internal.h.
set(API3_REWRITTEN_SUITES
    array-cvcl-02
    array-equality-retired-after-pop
    bv-abstraction-array-candidate-is-bound
    cnf-effort-flag
    fp-abstraction-flags
    incremental-scoped-preprocessing
    counter-enum-abi
    bv-abstraction-mult-schemas
    bv-abstraction-nary-plus
    array-extensionality
    array-ite
    b4-c2
    b4-c
    bvconst-width
    getbv
    hoangmle
    if-check
    incremental-auto-engage
    interface-check
    leaks
    persist-delete
    multiple-queries
    parsefile-using-cinterface
    parsestring-using-cinterface
    print
    multi-print
    push-no-pop
    push-pop
    push-pop-model
    reason-unknown
    refinement-flags
    incremental-query
    sbvdiv
    simplify
    stp-array-model
    stp-bool
    stpcheck
    stp-counterex
    stp-div-001
    stp-test3
    x
    y
    multi-query-bug
    reported_error
    stp-even-eqn-assert
    mdempsky
    counterexample
    example_broken
    counter-example-reading
    failing_solvermap
    bit_string
    check_sizes
    timeout-budget
    fp-model-reading
    fp-model-roundtrip
    fp-repeated-solve
    fp-shared-bv-operand
    fp-identity-passthrough
    fp-lowered-ite-fold
    fp-arithmetic
    fp-constants-conversions
    fp-multi-checker
    fp-cpp-wrapper
    fp-to-ieee-bv
    fp-roundingmode-var
    fp-roundingmode-survives-push-pop
    fp-roundingmode-model-completion
    fp-smt-equality
    fp-arrays
    fp-array-extensionality
    fp-model-eval-predicates
    fp-model-no-fp-in-query
    model-read-with-no-solve
    fp-printing
    cadical
    new-expr-kinds
    varexpr-widths
    uninterpreted-functions-api
    uninterpreted-functions-handle-safety
)
foreach(suite IN LISTS API3_REWRITTEN_SUITES)
    AddSTPGTest(api3-${suite}.cpp)
    target_include_directories(api3-${suite}Tests PRIVATE ${PROJECT_SOURCE_DIR}/lib)
    add_dependencies(api3-${suite}Tests stp_api_tables)
endforeach()
# The two suites that parse a CVC file from this directory.
set_property(TARGET api3-parsefile-using-cinterfaceTests APPEND PROPERTY
             COMPILE_DEFINITIONS CVC_FILE="${CMAKE_CURRENT_SOURCE_DIR}/t.cvc")
set_property(TARGET api3-stp-test3Tests APPEND PROPERTY
             COMPILE_DEFINITIONS CVC_FILE="${CMAKE_CURRENT_SOURCE_DIR}/f.cvc")

# The registry against the engine and the command line generated from it:
# reads lib/Api/Internal.h, and through it the tables tools/stp/main.cpp
# registers from (lib/Api/Registry.h).
AddSTPGTest(api3-registry.cpp)
target_include_directories(api3-registryTests PRIVATE ${PROJECT_SOURCE_DIR}/lib)
add_dependencies(api3-registryTests stp_api_tables)

# The stp binary's command line is generated from options.toml: its --help
# must list every entry with a CLI form, every alias and short flag, and every
# frontend row, and a sample of spellings must parse.
if(BUILD_EXECUTABLES)
    add_test(NAME api3-cli-help
             COMMAND ${PYTHON_EXECUTABLE}
                     ${PROJECT_SOURCE_DIR}/lib/Api/gen/check_cli_help.py
                     --stp $<TARGET_FILE:stp-bin>
                     --tables ${PROJECT_SOURCE_DIR}/lib/Api/tables)
endif()
