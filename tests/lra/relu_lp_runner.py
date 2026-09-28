#!/usr/bin/env python3
"""LP tightening must improve a phase, preserve strict boundaries and scope."""
import re
import sys
from relu_runner import source, relu, run


def main():
    solver = sys.argv[1]
    graph = ["(>= x (- 1))", "(<= x 1)", "(= y (- x))",
             "(= a (+ x y (/ 1 4)))", relu("a", "z")]
    # Interval a spans zero, and the initial triangle allows z > 1/4.
    # Optimizing a proves it positive; the rebuilt relaxation fixes z=1/4.
    query = source(graph + ["(or (> z (/ 1 4)) (< z 0))"])
    answer, log = run(solver, query, extra=("--lra-relu-lp=1",))
    assert answer == ["unsat"], log
    assert re.search(r"LRA ReLU LP: rounds=[1-9].*tightened=[1-9]", log), log
    assert "infeasible=1" in log, log
    for limit in ("--lra-relu-lp-seconds=0", "--lra-relu-lp-call-seconds=0"):
        answer, log = run(solver, query, extra=("--lra-relu-lp=1", limit))
        assert answer == ["unsat"], log  # normal solving still sees the query
        assert "rounds=0, calls=0, certificates=0" in log, log
        assert run(solver, source(graph + ["(= z (/ 1 4))"]),
                   extra=("--lra-relu-lp=1", limit))[0] == ["sat"]
    # Boundary equality is feasible; strictness cannot be inferred by rounding.
    for extra in ((), ("--lra-relu-lp=1",), ("--lra-relu-lp=1", "--lra-relu-lp-rounds=0")):
        assert run(solver, source(graph + ["(= z (/ 1 4))"]), extra=extra)[0] == ["sat"]
        assert run(solver, query, extra=extra)[0] == ["unsat"]
    incremental = source(graph).replace("(check-sat)", "") + """
(push 1)
(assert (or (> z (/ 1 4)) (< z 0)))
(check-sat)
(pop 1)
(check-sat)
"""
    assert run(solver, incremental, extra=("--lra-relu-lp=1",))[0] == ["unsat", "sat"]
    # A guarded input bound is not an unconditional LP box endpoint.
    unbounded = source([relu("x", "z"), "(or (<= x 0) (= z 2))", "(= x 2)"])
    assert run(solver, unbounded, extra=("--lra-relu-lp=1",))[0] == ["sat"]
    print("ReLU LP tightening, exact boundaries and scoping passed")


if __name__ == "__main__":
    main()
