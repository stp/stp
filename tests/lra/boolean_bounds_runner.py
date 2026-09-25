#!/usr/bin/env python3
"""Boolean interval hulls retain disjunctions, gaps, strictness and scope."""
import re
import sys
from relu_runner import source, relu, run


def main():
    solver = sys.argv[1]
    alternatives = "(or (and (>= x 1) (<= x 2)) (and (>= x 3) (<= x 4)))"
    for enabled in (0, 1):
        answer, log = run(solver, source([alternatives, relu("x", "y")]),
                          extra=(f"--lra-boolean-bounds={enabled}",))
        assert answer == ["sat"], log
        assert f"boolean_bounds={2 if enabled else 0}" in log, log
        assert f"relations=1, fixed={enabled}" in log, log
    cases = [
        ([alternatives, "(= x (/ 5 2))"], "unsat"),  # hull's gap is still excluded
        ([alternatives, "(> y 4)"], "unsat"),
        ([alternatives, "(= x 4)"], "sat"),
        (["(or (and (> x 0) (< x 1)) (and (> x 2) (< x 3)))", "(= x 0)"], "unsat"),
        (["(or (and (>= x 5) (<= x 4)) (and (>= x 1) (<= x 2)))", "(= x 2)"], "sat"),
        (["(or (and (>= x 5) (<= x 4)) (and (> x 1) (< x 1)))"], "unsat"),
        (["(or (and (>= x 1) (<= x 2)) (= z 10))", "(= x 100)"], "sat"),
        (["(or (<= x (- 1)) (>= x 1))", "(= x 100)"], "sat"),
        (["(or (<= x (- 1)) (>= x 1))", "(= x 0)"], "unsat"),
        (["(or (not (<= x 0)) (>= x 1))", "(= x 2)"], "sat"),
        (["(or (and (or (= x (- 1)) (= x 1)) (= z 2)) (and (>= x 2) (<= x 3) (= z 2)))", "(= x 0)"], "unsat"),
        (["(or (and (<= (* (- 2) x) (- 2)) (<= x 2)) (and (>= x 3) (<= x 4)))", "(= x 1)"], "sat"),
    ]
    # Independent one-dimensional interval-union oracle at exact integer points.
    for x in range(-5, 6):
        for a, b, c, d in ((-4, -2, 1, 3), (-2, 1, 0, 4), (0, 0, 2, 2)):
            def n(v): return f"(- {abs(v)})" if v < 0 else str(v)
            domain = f"(or (and (>= x {n(a)}) (<= x {n(b)})) (and (>= x {n(c)}) (<= x {n(d)})))"
            cases.append(([domain, f"(= x {n(x)})"], "sat" if a <= x <= b or c <= x <= d else "unsat"))
    for enabled in (0, 1):
        for floating in (0, 1):
            for clauses, expected in cases:
                answer, log = run(solver, source(clauses + [relu("x", "y")]), floating=floating,
                                  extra=(f"--lra-boolean-bounds={enabled}",))
                assert answer == [expected], (clauses, expected, answer, log)
    incremental = source([relu("x", "y")]).replace("(check-sat)", "") + f"""
(push 1)
(assert {alternatives})
(assert (> y 4))
(check-sat)
(pop 1)
(assert (= x 100))
(check-sat)
"""
    assert run(solver, incremental)[0] == ["unsat", "sat"]
    if sys.argv[2] == "ON":
        # Repeated input bounds inside a property OR now make the LP usable.
        guarded = source([relu("x", "y"), "(= a (- x))", relu("a", "z"),
                          "(or (and (>= x (- 1)) (<= x 1) (>= y 2)) (and (>= x (- 1)) (<= x 1) (>= z 2)))"])
        answer, log = run(solver, guarded, extra=("--lra-relu-lp=1",))
        assert answer == ["unsat"] and re.search(r"certificates=[1-9]", log), log
    print(f"PASS Boolean bounds: {len(cases)} interval-union cases, exact/float on/off, scope and LP engagement")


if __name__ == "__main__":
    main()
