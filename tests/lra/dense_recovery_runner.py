#!/usr/bin/env python3
"""Dense full-candidate recovery retains exact checking and bound scopes."""
from fractions import Fraction
import json
import re
import subprocess
import sys
from relu_runner import source, rat


def run(solver, text, enabled, floating=1):
    result = subprocess.run(
        [solver, "--SMTLIB2", "-s", f"--lra-dense-recovery={enabled}",
         f"--lra-float-driver={floating}", "--lra-verify-conflicts=1",
         "--lra-verify-canonical=1", *[f"--lra-presolve-{stage}=0" for stage in
         ("subst", "rows", "bounds", "propagate", "unconstrained")]],
        input=text, text=True, capture_output=True, timeout=60)
    assert result.returncode == 0, result.stderr[-4000:]
    answers = re.findall(r"^(sat|unsat|unknown)$", result.stdout, re.M)
    metrics = [json.loads(line[line.index("{"):]) for line in result.stderr.splitlines()
               if '"float_complete_recoveries"' in line]
    return answers, metrics, result.stderr


def main():
    solver = sys.argv[1]
    n = 128
    # Sylvester's Hadamard matrix is nonsingular, with a dyadic inverse.
    # It exercises dense pivot work without making the exact reference solve
    # expensive merely through unrelated rational denominator growth.
    matrix = [[-1 if (i & j).bit_count() % 2 else 1 for j in range(n)] for i in range(n)]
    assertions = [a for i in range(n) for a in (f"(>= x{i} (- 1))", f"(<= x{i} 1)")]
    for row in matrix:
        lhs = "(+ " + " ".join(f"(* {rat(c)} x{j})" for j, c in enumerate(row)) + ")"
        assertions.append(f"(= {lhs} {rat(Fraction(sum(row), 2))})")
    text = source(assertions, [f"x{i}" for i in range(n)])
    text += "(push 1)\n(assert (> x0 (/ 1 2)))\n(check-sat)\n(pop 1)\n(check-sat)\n"
    for enabled, floating in ((0, 1), (1, 1), (1, 0)):
        answers, metrics, log = run(solver, text, enabled, floating)
        assert answers == ["sat", "unsat", "sat"], (answers, log[-4000:])
        if enabled and floating:
            assert metrics and any(m["float_complete_recoveries"] > 0 for m in metrics), log
            assert any(m["float_factorized"] > 0 for m in metrics), log
    print("PASS dense recovery: exact dense solution, contradiction and retraction")


if __name__ == "__main__":
    main()
