#!/usr/bin/env python3
"""Substitution refusal must keep equations and publish exact source models."""
import re
import sys
from monotone_runner import NO_PRESOLVE, PREFIX, evaluate, expressions, run


def main():
    solver = sys.argv[1]
    cases = [
        ["(= x (+ y 1))", "(> x z)", "(< x (+ z 3))"],
        ["(= x (+ y 1))", "(= y (+ z 1))", "(> x 3)"],
        ["(= (+ (* 2 x) (* 3 y)) (+ z 1))", "(> x z)"],
        ["(= x (+ y 1))", "(= x (+ y 1))", "(> y 2)"],
    ]
    impossible = [
        ["(= x (+ y 1))", "(= x (+ y 2))"],
        ["(= (+ (* 2 x) (* 3 y)) 1)", "(= (+ (* 4 x) (* 6 y)) 3)"],
        ["(= x (+ y 1))", "(> y 2)", "(<= x 3)"],
    ]
    # Disabled, growth refusal, work refusal, and successful guarded rewriting.
    limits = ((0, 0), (1, 10000), (1000, 0), (1000, 10000))
    for driver in (0, 1):
        for growth, work in limits:
            for monotone in (0, 1):
                flags = (*NO_PRESOLVE, "--lra-presolve-subst=1",
                         f"--lra-presolve-subst-growth={growth}",
                         f"--lra-presolve-subst-work={work}",
                         "--lra-presolve-rounds=3", f"--lra-float-driver={driver}",
                         f"--lra-presolve-monotone={monotone}",
                         "--lra-model-reconstruction=off", "--incremental=off")
                for assertions in cases:
                    text = PREFIX + "\n".join(f"(assert {a})" for a in assertions)
                    output, log = run(solver, text + "\n(check-sat)\n(get-value (x y z))", flags)
                    assert output[0] == "sat", (assertions, flags, output, log)
                    values = {key.strip("|"): evaluate(value, {}) for key, value in output[1]}
                    assert all(evaluate(expressions(a)[0], values) for a in assertions), (
                        assertions, flags, values, log)
                    if growth == 0:
                        assert "LRA substitution round:" not in log, log
                    elif work == 0:
                        assert "refusals=1, stop=work" in log, log
                    elif growth == 1 and assertions != cases[-1]:
                        assert "refusals=1, stop=growth" in log, log
                    else:
                        assert "refusals=0, stop=none" in log, log
                for assertions in impossible:
                    text = PREFIX + "\n".join(f"(assert {a})" for a in assertions)
                    assert run(solver, text + "\n(check-sat)", flags)[0] == ["unsat"]

                # Each check-sat owns a fresh budget, including after a refusal,
                # a frame pop and a complete session reset.
                query = PREFIX + """
(assert (= x (+ y 1)))
(assert (> x z))
(assert (< x (+ z 3)))
(check-sat)
(push 1)
(assert (<= x z))
(check-sat)
(pop 1)
(check-sat)
(get-value (x y z))
(reset)
"""
                query += PREFIX + """
(assert (= x (+ y 1)))
(assert (> x z))
(assert (< x (+ z 3)))
(check-sat)
(get-value (x y z))
"""
                output, log = run(solver, query, flags)
                assert [x for x in output if isinstance(x, str)] == [
                    "sat", "unsat", "sat", "sat"], (flags, output, log)
                for model in (x for x in output if isinstance(x, list)):
                    values = {key.strip("|"): evaluate(value, {}) for key, value in model}
                    assert all(evaluate(expressions(a)[0], values) for a in cases[0]), values
                if growth:
                    first_rounds = re.findall(r"LRA substitution round: index=1, (.*)", log)
                    assert len(first_rounds) == 4, log
                    assert first_rounds[0] == first_rounds[2] == first_rounds[3], log
    print("PASS substitution guards: exact/float models, Gaussian equations, refusal and query scope")


if __name__ == "__main__":
    main()
