#!/usr/bin/env python3
"""Compare persistent arithmetic with fresh solves, and require actual reuse."""

import json
import subprocess
import sys


def run(solver, source, flags):
    result = subprocess.run(
        [solver, "--SMTLIB2", "--lra-verify-conflicts=1",
         "--lra-verify-canonical=1", "-s", *flags],
        input=source, text=True, capture_output=True, timeout=120)
    answers = [line for line in result.stdout.splitlines()
               if line in ("sat", "unsat", "unknown", "unsupported")]
    metrics = [json.loads(line.split("LRA-METRICS ", 1)[1])
               for line in result.stderr.splitlines() if line.startswith("LRA-METRICS ")]
    if result.returncode or any(a in ("unknown", "unsupported") for a in answers):
        raise AssertionError((flags, result.stdout[-4000:], result.stderr[-8000:]))
    return answers, metrics


def main():
    solver = sys.argv[1]
    # The first Real check has an empty base. Variables enter the arithmetic
    # core as they first occur in assertions, after earlier rows have pivoted.
    source = """
(set-logic QF_LRA)
(set-option :produce-models true)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)
(push 1)
(assert (>= x 1))
(check-sat)
(assert (= y (/ 2 3)))
(check-sat)
(get-value (y))
(push 1)
(assert (< (+ x y) 1))
(check-sat)
(pop 1)
(check-sat)
(assert (= z (/ 7 3)))
(check-sat)
(get-value (y z))
(push 1)
(assert (> y 1))
(check-sat)
(pop 1)
(assert (>= (+ x z) 6))
(check-sat)
(pop 1)
(assert (>= x 0))
"""
    expected = ["sat", "sat", "unsat", "sat", "sat", "unsat", "sat"]
    for i in range(1, 31):
        source += f"""
(push 1)
(assert (>= x {i}))
(assert (<= x {i + 1}))
(check-sat)
(assert (< x {i}))
(check-sat)
(pop 1)
(assert (<= y {1000 + i}))
(check-sat)
"""
        expected += ["sat", "unsat", "sat"]
    # Reset destroys a session; a new symbol with an old printed name must
    # acquire a fresh identity and must not inherit a retired bound.
    source += """
(reset)
(set-logic QF_LRA)
(declare-fun x () Real)
(assert (< x (- 10)))
(check-sat)
(exit)
"""
    expected.append("sat")
    baseline, _ = run(solver, source, ["--incremental=off"])
    assert baseline == expected, ("baseline", baseline, expected)
    for floating in (0, 1):
        for optimize in (0, 1):
            flags = ["--incremental=on", "--lra-persistent-state=1",
                     f"--lra-float-driver={floating}", f"--lra-soi={optimize}",
                     f"--lra-early-conflicts={optimize}", *sys.argv[2:]]
            actual, metrics = run(solver, source, flags)
            assert actual == expected, (flags, actual, expected)
            summary = [{key: m.get(key) for key in
                        ("failure", "persistent_extensions", "float_extensions", "core_rebuilds")}
                       for m in metrics]
            # A silent decline to batch solving must not pass this test.
            assert max(m.get("persistent_extensions", 0) for m in metrics) >= 30, summary
            if floating:
                assert max(m.get("float_extensions", 0) for m in metrics) >= 30, summary
            assert all(not m["failure"] for m in metrics), summary
            assert all(m["core_rebuilds"] == 1 for m in metrics
                       if m.get("persistent_extensions", 0)), summary
    print(f"PASS persistent session: {len(expected)} checks in five configurations")


if __name__ == "__main__":
    main()
