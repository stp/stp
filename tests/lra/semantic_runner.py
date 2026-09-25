#!/usr/bin/env python3
"""Black-box semantic/context matrix for one configured SAT backend."""

from __future__ import annotations

import json
import pathlib
import subprocess
import sys


# Conflict-certificate verification is off in the shipped solver -- it is a
# self-check, not a solving step. The tests are where it earns its keep, so
# every case below runs with it on.
VERIFY = "--lra-verify-conflicts=1"
# The number layer's canonical-form self-check. Off in the shipped solver, on
# here: this is the run that is supposed to be paying for it.
CANONICAL = "--lra-verify-canonical=1"


def statuses(output: str) -> list[str]:
    return [line.strip() for line in output.splitlines()
            if line.strip() in {"sat", "unsat", "unknown", "unsupported"}]


def main() -> int:
    if len(sys.argv) < 2:
        raise SystemExit("usage: semantic_runner.py STP [BACKEND [SOLVER_FLAGS...]]")
    solver = pathlib.Path(sys.argv[1]).resolve()
    backend = sys.argv[2] if len(sys.argv) >= 3 else "configured"
    solver_flags = sys.argv[3:]
    huge = "1" + "0" * 1234  # 4,102 bits: floor(log2(10^1234))+1.

    cases: list[tuple[str, str, list[str], list[str], list[str]]] = [
        ("relations-positive", """
          (set-logic QF_LRA)
          (declare-const x Real)
          (assert (< x 1)) (assert (<= x 1))
          (assert (> x (- 2))) (assert (>= x (- 2)))
          (check-sat)
        """, ["sat"], [], []),
        ("relations-negative", """
          (set-logic QF_LRA)
          (declare-const x Real)
          (assert (not (< x 1))) (assert (not (> x 2)))
          (assert (not (<= x 0))) (assert (not (>= x 3)))
          (check-sat)
        """, ["sat"], [], []),
        ("strict-boundary-unsat", """
          (set-logic QF_LRA) (declare-const x Real)
          (assert (< x 1)) (assert (>= x 1)) (check-sat)
        """, ["unsat"], [], []),
        ("strict-open-exact-model", """
          (set-logic QF_LRA) (set-option :produce-models true)
          (declare-const x Real)
          (assert (> x 0)) (assert (< x 1))
          (check-sat) (get-value (x))
        """, ["sat"], ["(|x| (/ 1 4))"], []),
        ("decimal-rational-alias-scale", """
          (set-logic QF_LRA) (set-option :produce-models true)
          (declare-const x Real) (declare-const y Real)
          (assert (= x 0.1250))
          (assert (= y (/ 1 8)))
          (assert (= (* 16 x) 2))
          (assert (= (+ x y) (/ 1 4)))
          (assert (<= (+ x y) (/ 2 8)))
          (check-sat) (get-value (x y (+ x y)))
        """, ["sat"], ["(|x| (/ 1 8))", "((+ |x| |y|) (/ 1 4))"], []),
        ("free-redundant-duplicate-aliased", """
          (set-logic QF_LRA) (set-option :produce-models true)
          (declare-const x Real) (declare-const free Real)
          (assert (= x 2)) (assert (= x 2))
          (assert (= (+ x x) 4)) (assert (= (* 3 x) 6))
          (check-sat) (get-value (x free))
        """, ["sat"], ["(|x| 2)", "(|free| 0)"], []),
        ("unconstrained-real-only", """
          (set-logic QF_LRA) (set-option :produce-models true)
          (declare-const unconstrained Real)
          (check-sat) (get-value (unconstrained))
        """, ["sat"], ["(|unconstrained| 0)"], []),
        ("equality-definition", """
          (set-logic QF_LRA) (declare-const x Real) (declare-const y Real)
          (assert (not (= (= x y) (and (<= x y) (>= x y)))))
          (check-sat)
        """, ["unsat"], [], []),
        ("false-equality-less-branch", """
          (set-logic QF_LRA) (declare-const x Real) (declare-const y Real)
          (assert (not (= x y))) (assert (< x y)) (check-sat)
        """, ["sat"], [], []),
        ("false-equality-greater-branch", """
          (set-logic QF_LRA) (declare-const x Real) (declare-const y Real)
          (assert (not (= x y))) (assert (> x y)) (check-sat)
        """, ["sat"], [], []),
        ("direct-negated-equality", """
          (set-logic QF_LRA) (declare-const x Real) (declare-const y Real)
          (assert (not (= x y))) (assert (= x y)) (check-sat)
        """, ["unsat"], [], []),
        ("pairwise-distinct", """
          (set-logic QF_LRA)
          (declare-const x Real) (declare-const y Real) (declare-const z Real)
          (assert (= x 0)) (assert (= y 1)) (assert (= z 2))
          (assert (distinct x y z)) (check-sat)
          (push 1) (assert (= z x)) (check-sat) (pop 1)
        """, ["sat", "unsat"], [], []),
        ("constant-predicates", """
          (set-logic QF_LRA)
          (push 1) (assert (< 0 1)) (check-sat) (pop 1)
          (push 1) (assert (> 0 1)) (check-sat) (pop 1)
        """, ["sat", "unsat"], [], []),
        ("huge-4102-bit-model", f"""
          (set-logic QF_LRA) (set-option :produce-models true)
          (declare-const x Real)
          (assert (= x {huge})) (check-sat) (get-value (x))
        """, ["sat"], [huge], []),
        ("multiple-lra-conflicts-before-model", """
          (set-logic QF_LRA) (set-option :produce-models true)
          (declare-const x Real)
          (assert (or (and (< x 0) (>= x 0))
                      (and (> x 1) (<= x 1))
                      (and (< x (- 1)) (>= x (- 1)))
                      (= x 7)))
          (check-sat) (get-value (x))
        """, ["sat"], ["(|x| 7)"], []),
        ("abstraction-unsat-after-nogoods", """
          (set-logic QF_LRA) (declare-const x Real)
          (assert (or (and (< x 0) (>= x 0))
                      (and (> x 1) (<= x 1))))
          (check-sat)
        """, ["unsat"], [], []),
        ("contexts-assumptions-reset", """
          (set-logic QF_LRA) (declare-const x Real)
          (assert (= x 1))
          (check-sat) (check-sat)
          (push 1) (assert (> x 2)) (check-sat) (pop 1)
          (check-sat-assuming ((>= x 1)))
          (get-value (x))
          (check-sat-assuming ((> x 2)))
          (check-sat)
          (reset-assertions)
          (declare-const y Real) (assert (= y (/ 5 7))) (check-sat)
          (reset)
          (set-logic QF_LRA) (declare-const z Real)
          (assert (< z 0)) (check-sat)
        """, ["sat", "sat", "unsat", "sat", "unsat", "sat", "sat", "sat"],
        ["(|x| 1)"], []),
        ("scoped-model-printing-full-reset", """
          (set-logic QF_LRA) (set-option :produce-models true)
          (declare-const x Real) (assert (= x 1))
          (push 1) (declare-const scoped Real) (assert (= scoped 2))
          (check-sat) (get-model) (pop 1)
          (check-sat) (get-model)
          (reset)
          (set-logic QF_LRA) (set-option :produce-models true)
          (declare-const fresh Real) (assert (= fresh (/ 3 5)))
          (check-sat) (get-model)
        """, ["sat", "sat", "sat"],
        ["(define-fun |x| () Real 1)",
         "(define-fun |fresh| () Real (/ 3 5))"], []),
        ("mixed-bv-lra", """
          (declare-const x Real) (declare-const b (_ BitVec 4))
          (assert (or (< x 0) (= b #b1010)))
          (assert (not (< x 0))) (assert (= b #b1010))
          (check-sat)
        """, ["sat"], [], []),
        ("mixed-fp-lra", """
          (declare-const x Real)
          (declare-const f (_ FloatingPoint 8 24))
          (assert (= x (/ 3 2)))
          (assert (fp.eq f ((_ to_fp 8 24) #x3f800000)))
          (check-sat)
        """, ["sat"], [], []),
        ("lra-array-both-consistent", """
          (declare-const x Real)
          (declare-const a (Array (_ BitVec 2) (_ BitVec 4)))
          (declare-const b (Array (_ BitVec 2) (_ BitVec 4)))
          (assert (= x 1)) (assert (= a b))
          (assert (= (select a #b00) #b0011))
          (assert (= (select b #b00) #b0011))
          (check-sat)
        """, ["sat"], [], ["--array-equality"]),
        ("lra-consistent-array-conflict", """
          (declare-const x Real)
          (declare-const a (Array (_ BitVec 2) (_ BitVec 4)))
          (declare-const b (Array (_ BitVec 2) (_ BitVec 4)))
          (assert (= x 1)) (assert (= a b))
          (assert (= (select a #b00) #b0011))
          (assert (= (select b #b00) #b0100))
          (check-sat)
        """, ["unsat"], [], ["--array-equality"]),
        ("lra-conflict-array-consistent", """
          (declare-const x Real)
          (declare-const a (Array (_ BitVec 2) (_ BitVec 4)))
          (declare-const b (Array (_ BitVec 2) (_ BitVec 4)))
          (assert (< x 0)) (assert (>= x 0)) (assert (= a b))
          (check-sat)
        """, ["unsat"], [], ["--array-equality"]),
        ("lra-array-both-conflict", """
          (declare-const x Real)
          (declare-const a (Array (_ BitVec 2) (_ BitVec 4)))
          (declare-const b (Array (_ BitVec 2) (_ BitVec 4)))
          (assert (< x 0)) (assert (>= x 0)) (assert (= a b))
          (assert (= (select a #b00) #b0011))
          (assert (= (select b #b00) #b0100))
          (check-sat)
        """, ["unsat"], [], ["--array-equality"]),
        ("legacy-array-refinement-after-lra-stage", """
          (declare-const x Real)
          (declare-const a (Array (_ BitVec 4) (_ BitVec 4)))
          (declare-const i (_ BitVec 4)) (declare-const j (_ BitVec 4))
          (assert (= x (/ 9 4)))
          (assert (= i j))
          (assert (distinct (select a i) (select a j)))
          (assert (= (select a #x0) (select a #x0)))
          (assert (= (select a #x1) (select a #x1)))
          (assert (= (select a #x2) (select a #x2)))
          (assert (= (select a #x3) (select a #x3)))
          (assert (= (select a #x4) (select a #x4)))
          (assert (= (select a #x5) (select a #x5)))
          (assert (= (select a #x6) (select a #x6)))
          (assert (= (select a #x7) (select a #x7)))
          (assert (= (select a #x8) (select a #x8)))
          (assert (= (select a #x9) (select a #x9)))
          (check-sat)
        """, ["unsat"], [], []),
    ]

    # For Reals, SMT-LIB advertises only the standard QF_LRA and QF_UFLRA
    # logics.  The disjoint combinations below are deliberately exercised
    # through the unrestricted public construction API by the
    # lra_combination_api test; retaining their inputs here documents that no
    # invented combined logic is claimed.
    api_only = {
        "mixed-bv-lra", "mixed-fp-lra", "lra-array-both-consistent",
        "lra-consistent-array-conflict", "lra-conflict-array-consistent",
        "lra-array-both-conflict", "legacy-array-refinement-after-lra-stage",
    }
    cases = [case for case in cases if case[0] not in api_only]

    results = []
    failures = []
    for name, source, expected, contains, extra_args in cases:
        completed = subprocess.run(
            [str(solver), *solver_flags, *extra_args, VERIFY, CANONICAL, "--SMTLIB2"], input=source,
            text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            check=False, timeout=120)
        combined = completed.stdout + completed.stderr
        actual = statuses(completed.stdout)
        passed = (completed.returncode == 0 and actual == expected and
                  all(fragment in completed.stdout for fragment in contains) and
                  "unknown" not in actual and "unsupported" not in actual)
        if name == "scoped-model-printing-full-reset":
            passed = (passed and
                      completed.stdout.count("(define-fun |scoped|") == 1 and
                      completed.stdout.count("(define-fun |x|") == 2 and
                      completed.stdout.count("(define-fun |fresh|") == 1)
        results.append({"name": name, "expected": expected, "actual": actual,
                        "return_code": completed.returncode,
                        "passed": passed})
        if not passed:
            failures.append({"name": name, "output": combined[-4000:]})

    # The same matrix again, with the theory riding inside the SAT search
    # instead of judging complete models after it. Driving the search is a
    # different path through the coordinator, the adapter and the core, but
    # it answers the same question, so every verdict has to match. Only the
    # verdicts: a different search order may land on a different model, and
    # any of them is a correct answer.
    for name, source, expected, _contains, extra_args in cases:
        completed = subprocess.run(
            [str(solver), *solver_flags, *extra_args, VERIFY, CANONICAL,
             "--lra-theory-propagation=1", "--SMTLIB2"],
            input=source, text=True, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, check=False, timeout=120)
        combined = completed.stdout + completed.stderr
        actual = statuses(completed.stdout)
        passed = (completed.returncode == 0 and actual == expected and
                  "unknown" not in actual and "unsupported" not in actual)
        results.append({"name": f"propagating:{name}", "expected": expected,
                        "actual": actual,
                        "return_code": completed.returncode,
                        "passed": passed})
        if not passed:
            failures.append({"name": f"propagating:{name}",
                             "output": combined[-4000:]})

    # Reject an invented mixed-logic name explicitly; combined disjoint
    # construction is available only through the unrestricted public API.
    mixed_logic = subprocess.run(
        [str(solver), "--SMTLIB2"],
        input="(set-logic QF_BV_LRA)\n(exit)\n", text=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False,
        timeout=120)
    mixed_output = mixed_logic.stdout + mixed_logic.stderr
    # A logic STP cannot decide is refused and ends the session non-zero; the
    # message names the offending token.
    mixed_passed = ("unknown logic" in mixed_output and
                    "QF_BV_LRA" in mixed_output and
                    mixed_logic.returncode != 0)
    results.append({"name": "unsupported-combined-logic",
                    "expected": ["input-error"],
                    "actual": (["input-error"] if mixed_passed else []),
                    "return_code": mixed_logic.returncode,
                    "passed": mixed_passed})
    if not mixed_passed:
        failures.append({"name": "unsupported-combined-logic",
                         "output": mixed_output[-4000:]})

    summary = {"backend": backend,
               "case_total": len(results),
               "case_passed": sum(1 for result in results if result["passed"]),
               "failed": failures, "results": results,
               "passed": not failures}
    print(json.dumps(summary, sort_keys=True))
    return 0 if not failures else 1


if __name__ == "__main__":
    sys.exit(main())
