#!/usr/bin/env python3
"""Exercise recovery through the float/SAT bridge, with exact audits on."""

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
    recovered = 0
    for width in (8, 32):
        declarations = "\n".join(f"(declare-const x{i} Real)" for i in range(width))
        bounds = "\n".join(f"(assert (>= x{i} 1))" for i in range(width))
        terms = " ".join(f"(* (/ {1073741823-i} 1073741824) x{i})"
                         for i in range(width))
        source = f"""
(set-logic QF_LRA)
{declarations}
{bounds}
(push 1)
(assert (<= (+ {terms}) 0))
(check-sat)
(pop 1)
(check-sat)
"""
        for setting in (None, 0, 1):
            flags = [f"--lra-presolve-{stage}=0" for stage in
                     ("subst", "bounds", "rows", "propagate", "unconstrained")]
            if setting is not None:
                flags.append(f"--lra-conflict-recovery={setting}")
            answers, metrics = run(sys.argv[1], source, flags)
            assert answers == ["unsat", "sat"], (setting, width, answers)
            attempts = sum(m["conflict_recovery_attempts"] for m in metrics)
            successes = sum(m["conflict_recoveries"] for m in metrics)
            if setting == 0:
                assert attempts == successes == 0, metrics
            else:
                recovered += successes
                assert attempts >= successes > 0, metrics
                assert all(m["float_certificate_failed"] == 0 for m in metrics), metrics
    assert recovered > 0, "fixtures did not exercise certificate recovery"
    print("PASS conflict recovery: default/on/off, dense dyadics, UNSAT then SAT")


if __name__ == "__main__":
    main()
