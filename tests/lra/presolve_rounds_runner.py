#!/usr/bin/env python3
"""Factorial controls for presolve repetition and monotone elimination."""
import sys
from monotone_runner import CASES, PREFIX, evaluate, expressions, run


def main():
    solver = sys.argv[1]
    for rounds in (1, 3):
        for monotone in (0, 1):
            for driver in (0, 1):
                for assertions in CASES:
                    flags = (f"--lra-presolve-rounds={rounds}",
                             f"--lra-presolve-monotone={monotone}",
                             f"--lra-float-driver={driver}",
                             "--lra-model-reconstruction=on")
                    text = PREFIX + "\n".join(f"(assert {a})" for a in assertions)
                    output, log = run(solver, text + "\n(check-sat)\n(get-value (x y z b))", flags)
                    assert output[0] == "sat", (assertions, flags, output, log)
                    values = {key.strip("|"): evaluate(value, {}) for key, value in output[1]}
                    assert all(evaluate(expressions(a)[0], values) for a in assertions), (
                        assertions, flags, values, log)
                unsat = PREFIX + "(assert (> x y))\n(assert (<= x y))\n(check-sat)"
                assert run(solver, unsat, flags)[0] == ["unsat"]
    print("PASS presolve factorial controls: repetition, monotone, exact/float and reconstruction")


if __name__ == "__main__":
    main()
