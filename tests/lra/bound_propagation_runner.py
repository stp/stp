#!/usr/bin/env python3
"""Check online bound implications against exact interval answers and scope."""

import re
import subprocess
import sys


def solve(binary, text, online, floating):
    result = subprocess.run(
        [binary, "--SMTLIB2", "--cadical", "--lra-first-search=1",
         f"--lra-bound-propagation={int(online)}",
         f"--lra-float-driver={int(floating)}"],
        input=text, capture_output=True, text=True, timeout=30)
    assert result.returncode == 0, result.stderr[-3000:]
    return re.findall(r"^(sat|unsat|unknown)$", result.stdout, re.M)


def main():
    binary = sys.argv[1]
    header = "(set-logic QF_LRA)\n(declare-fun x () Real)\n(declare-fun y () Real)\n"
    # Two open/closed intervals. Check exact endpoints as well as the gap;
    # each Boolean branch carries multiple bounds on the same canonical row.
    cases = []
    for x in range(-3, 5):
        term = str(x) if x >= 0 else f"(- {-x})"
        formula = (header +
                   "(assert (or (and (> x (- 2)) (<= x 0)) "
                   "(and (>= x 2) (< x 4))))\n" +
                   f"(assert (= x {term}))\n(check-sat)\n")
        expected = "sat" if -2 < x <= 0 or 2 <= x < 4 else "unsat"
        cases.append((formula, [expected]))

    # A shared affine row with opposite inequality polarities.
    affine = header + "(assert (= y 0))\n"
    cases.extend([
        (affine + "(assert (<= (+ (* 2 x) y) 0))\n"
         "(assert (or (> (+ (* 2 x) y) 1) (= x 0)))\n"
         "(assert (not (= x 0)))\n(check-sat)\n", ["unsat"]),
        (affine + "(assert (< (+ (* 2 x) y) 1))\n"
         "(assert (or (<= (+ (* 2 x) y) 1) (> x 5)))\n"
         "(assert (= x 0))\n(check-sat)\n", ["sat"]),
    ])
    # An implication learned under one assertion frame must not survive a
    # pop into the next query.
    incremental = (header + "(push 1)\n(assert (<= x 0))\n"
                   "(assert (> x 1))\n(check-sat)\n(pop 1)\n"
                   "(push 1)\n(assert (> x 1))\n(check-sat)\n(pop 1)\n"
                   "(check-sat)\n")
    cases.append((incremental, ["unsat", "sat", "sat"]))

    for online in (False, True):
        for floating in (False, True):
            for text, expected in cases:
                answer = solve(binary, text, online, floating)
                assert answer == expected, (online, floating, expected, answer, text)
    print(f"PASS bound propagation: {len(cases)} cases with both drivers and both delivery paths")


if __name__ == "__main__":
    main()
