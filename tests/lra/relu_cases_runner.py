#!/usr/bin/env python3
"""Conditional boxes may refute an alternative, never constrain other arms."""
from fractions import Fraction
import random
import re
import sys
from relu_runner import relu, source, run, rat


def main():
    solver = sys.argv[1]
    flags = ("--lra-relu-cases=1",)
    graph = [relu("x", "y"), relu("x", "z")]
    # Opposite input intervals require different phases. The difference is
    # identically zero, which independent output intervals cannot express.
    arms = ["(and (>= x (- 2)) (<= x (- 1)) (> (- y z) 0))",
            "(and (>= x 1) (<= x 2) (< (- y z) 0))"]
    query = source(graph + [f"(or {' '.join(arms)})"])
    for floating in (0, 1):
        answer, log = run(solver, query, floating=floating, extra=flags)
        assert answer == ["unsat"], log
        assert "LRA ReLU cases: checked=2, closed=2" in log, log
    for enabled in (0, 1):
        # A feasible zero boundary, an unbounded arm, and an unknown Boolean
        # guard must each survive alongside the refuted alternatives.
        for last in ("(and (= x 0) (= y z))", "(and (> x 20) (= y z))",
                     "(and (= x 0) (not (> y z)))"):
            text = source(graph + [f"(or {' '.join(arms)} {last})"])
            assert run(solver, text, extra=(f"--lra-relu-cases={enabled}",))[0] == ["sat"]
        # A still-ambiguous phase is not a refutation.
        text = source(graph + ["(or (and (>= x (- 1)) (<= x 1) (= y 0)) "
                               "(and (= x 3) (< y 0)))"])
        assert run(solver, text, extra=(f"--lra-relu-cases={enabled}",))[0] == ["sat"]
    # Partially covered disjunctions keep every unchecked alternative.
    partial = source(graph + [f"(or {' '.join(arms)} (and (= x 0) (= y z)))"])
    answer, log = run(solver, partial, extra=flags)
    assert answer == ["sat"] and "checked=3, closed=2" in log, log
    repeated = source(graph + [f"(or {' '.join(arms)} (and (>= x 1) (<= x 2) (= y z)))"])
    answer, log = run(solver, repeated, extra=flags)
    assert answer == ["sat"] and "cache_hits=1" in log, log
    answer, log = run(solver, query, extra=flags + ("--lra-relu-cases-seconds=0",))
    assert answer == ["unsat"] and "LRA ReLU cases:" not in log, log
    truncated = [f"(and (= x {rat(i)}) (> (- y z) 0))" for i in range(-256, 257)]
    answer, log = run(solver, source(graph + [f"(or {' '.join(truncated)})"]), extra=flags)
    assert answer == ["unsat"], log
    assert "checked=512, closed=512" in log and "limited=1" in log, log
    # Cyclic affine definitions are left to ordinary arithmetic. A valid
    # source does not require the selected defining equations to be acyclic.
    cyclic = source(["(= a (+ x 1))", "(= x (- a 1))", relu("x", "y"),
                     "(or (and (= x (- 1)) (= y 0)) (and (= x 1) (= y 1)))"])
    assert run(solver, cyclic, extra=flags)[0] == ["sat"]
    # Nested alternatives, strictness, equality, and gaps are all preserved.
    for relation, point, expected in (("<", "0", "unsat"),
                                      ("<=", "0", "sat"),
                                      ("=", "0", "sat"),
                                      ("=", "(/ 1 4)", "unsat")):
        a = f"(and (> x (- 2)) (< x (- 1)) ({relation} (- y z) {point}))"
        b = f"(and (> x 1) (< x 2) ({relation} (- y z) {point}))"
        text = source(graph + [f"(or (or {a} {b}) (and (= x 0) (> y 0)))"])
        assert run(solver, text, extra=flags)[0] == [expected]
    incremental = source(graph).replace("(check-sat)", "") + f"""
(push 1)
(assert (or {' '.join(arms)}))
(check-sat)
(pop 1)
(push 1)
(assert (= x 0))
(check-sat)
(pop 1)
(check-sat)
"""
    assert run(solver, incremental, extra=flags)[0] == ["unsat", "sat", "sat"]
    # Random two-input, two-layer graphs. Each arm pins an independently
    # evaluated rational point, so raising every output lower bound makes
    # UNSAT, while retaining one exact value provides a known SAT witness.
    rng = random.Random(8531)
    closed = 0
    for case in range(40):
        a, b, c, d, e = [Fraction(rng.randrange(-4, 5), 3) for _ in range(5)]
        graph = [f"(= p (+ (* {rat(a)} x) (* {rat(b)} z) {rat(c)}))",
                 relu("p", "r"), f"(= q (+ (* {rat(d)} r) {rat(e)}))", relu("q", "y")]
        arms = []
        for i, (x, z) in enumerate(((Fraction(-1), Fraction(2)),
                                     (Fraction(2), Fraction(-1)),
                                     (Fraction(1, 3), Fraction(1, 4)))):
            expected = max(d * max(a*x + b*z + c, 0) + e, 0)
            offset = Fraction(1, 7) if case % 2 or i != 2 else Fraction(0)
            arms.append(f"(and (= x {rat(x)}) (= z {rat(z)}) (>= y {rat(expected + offset)}))")
        query = source(graph + [f"(or {' '.join(arms)})"], ("x", "z", "p", "r", "q", "y"))
        for enabled in (0, 1):
            answer, log = run(solver, query, floating=int(case % 3 != 0),
                              extra=(f"--lra-relu-cases={enabled}",))
            assert answer == ["unsat" if case % 2 else "sat"], (query, log)
            match = re.search(r"LRA ReLU cases: .*closed=(\d+)", log)
            if match:
                closed += int(match[1])
    assert closed > 0, "randomized cases did not engage conditional proofs"
    print("ReLU conditional affine boxes, strictness, retained arms and scope passed")


if __name__ == "__main__":
    main()
