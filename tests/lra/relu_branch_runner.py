#!/usr/bin/env python3
"""Check complete phase coverage, conditional clauses and zero boundaries."""
import re
import random
from fractions import Fraction
import sys
from relu_runner import source, relu, run, rat


def main():
    solver = sys.argv[1]
    # Two copies of a ReLU can disagree in their common triangle relaxation.
    # Splitting their shared preactivation forces them equal in both phases.
    graph = ["(>= x (- 1))", "(<= x 1)", relu("x", "y"), relu("x", "z")]
    query = source(graph + ["(>= (- y z) (/ 1 4))"])
    flags = ("--lra-relu-branch=1",)
    answer, log = run(solver, query, extra=flags)
    assert answer == ["unsat"], log
    assert "nodes=3, splits=1, closed=2, open=0" in log, log
    assert "clauses=2, infeasible=1" in log, log
    # Every property arm is its own conditional root. Optimizing only the
    # network would leave this relaxation feasible indefinitely.
    bad = "(>= (- y z) (/ 1 4))"
    other_bad = "(>= (- z y) (/ 1 4))"
    disjunctive = source(graph + [f"(or {bad} {other_bad})"])
    answer, log = run(solver, disjunctive, extra=flags)
    assert answer == ["unsat"], log
    assert "nodes=6, splits=2, closed=4, open=0" in log, log
    assert "property_roots=2" in log, log
    answer, log = run(solver, disjunctive,
                      extra=flags + ("--lra-relu-branch-nodes=3",))
    assert answer == ["unsat"], log  # remaining root goes to ordinary solving
    assert "nodes=3, splits=1, closed=2, open=1" in log, log
    assert "infeasible=0, property_roots=2" in log, log
    # Closing the bad output root must not discard the feasible other root.
    # With pinned inputs, omitting the property guard would learn FALSE.
    for x in (-1, 0, 1):
        for floating in (0, 1):
            for property_on in (0, 1):
                for first in (bad, "(> (- y z) (/ 1 4))",
                              f"(and {bad} (<= x 0))"):
                    text = source(graph + [f"(= x {rat(x)})",
                                           f"(or {first} (= y z))"])
                    assert run(solver, text, floating=floating,
                               extra=flags + (f"--lra-relu-property-branches={property_on}",))[0] == ["sat"]
    opaque = source(graph + [f"(or {bad} choice)"])
    opaque = opaque.replace("(set-logic QF_LRA)",
                            "(set-logic QF_LRA)\n(declare-fun choice () Bool)")
    answer, log = run(solver, opaque, extra=flags)
    assert answer == ["sat"] and "property_roots=0" in log, log
    property_scope = source(graph).replace("(check-sat)", "") + f"""
(push 1)
(assert (or {bad} {other_bad}))
(check-sat)
(pop 1)
(push 1)
(assert (= x 0))
(assert (or {bad} (= y z)))
(check-sat)
(pop 1)
(check-sat)
"""
    assert run(solver, property_scope, extra=flags)[0] == ["unsat", "sat", "sat"]
    for limit in ("--lra-relu-branch-seconds=0", "--lra-relu-lp-call-seconds=0"):
        answer, log = run(solver, query, extra=flags + (limit,))
        assert answer == ["unsat"], log
        assert "nodes=0, splits=0, closed=0, open=1" in log, log
        assert "clauses=0, infeasible=0" in log, log
        assert run(solver, source(graph + ["(= y z)"]),
                   extra=flags + (limit,))[0] == ["sat"]
    # One closed child is a conditional lemma, not an unconditional conflict.
    answer, log = run(solver, query, extra=flags + ("--lra-relu-branch-nodes=2",))
    assert answer == ["unsat"], log  # ordinary solving finishes from the lemma
    assert "nodes=2, splits=1, closed=1, open=1" in log, log
    assert "clauses=1, infeasible=0" in log, log
    for nodes in (0, 1, 2, 128):
        for floating in (0, 1):
            for x in (-1, 0, 1):
                point = f"(- {abs(x)})" if x < 0 else str(x)
                sat = source(graph + [f"(= x {point})", "(= y z)"])
                answer, log = run(solver, sat, floating=floating,
                                  extra=flags + (f"--lra-relu-branch-nodes={nodes}",))
                assert answer == ["sat"], log
    incremental = source(graph).replace("(check-sat)", "") + """
(push 1)
(assert (>= (- y z) (/ 1 4)))
(check-sat)
(pop 1)
(push 1)
(assert (= x 0))
(assert (= y z))
(check-sat)
(pop 1)
(check-sat)
"""
    assert run(solver, incremental, extra=flags)[0] == ["unsat", "sat", "sat"]
    # No asserted input box: the LP must abstain, and ordinary solving decides.
    assert run(solver, source([relu("x", "y"), "(> x 100)"]), extra=flags)[0] == ["sat"]
    # Preserve known exact witnesses while allowing the LP to try other
    # phases. This exercises closed branches of SAT queries, where an omitted
    # assumption or incorrectly complemented guard would discard a solution.
    rng = random.Random(9250)
    closed_sat_branches = 0
    for _ in range(64):
        clauses = ["(>= x (- 1))", "(<= x 1)", "(>= y (- 1))", "(<= y 1)"]
        values = []
        for i in range(4):
            a, b, c = [rng.randrange(-3, 4) for _ in range(3)]
            clauses += [f"(= p{i} (+ (* {rat(a)} x) (* {rat(b)} y) {rat(c)}))",
                        relu(f"p{i}", f"r{i}")]
            values.append(max(a*Fraction(1, 3) - b*Fraction(1, 4) + c, 0))
        for _ in range(3):
            weights = [rng.choice((-3, -1, 1, 3)) for _ in range(4)]
            rhs = sum(a*b for a, b in zip(weights, values)) + Fraction(1, 16)
            terms = " ".join(f"(* {rat(a)} r{i})" for i, a in enumerate(weights))
            clauses.append(f"(<= (+ {terms}) {rat(rhs)})")
        text = source(clauses, ("x", "y", *[f"{s}{i}" for i in range(4) for s in ("p", "r")]))
        answer, log = run(solver, text, extra=flags + ("--lra-relu-branch-nodes=8",))
        assert answer == ["sat"], (text, log)
        match = re.search(r"LRA ReLU branch: .*closed=(\d+)", log)
        if match:
            closed_sat_branches += int(match[1])
    assert closed_sat_branches > 0, "random SAT cases did not exercise conditional conflicts"
    print("ReLU complete/partial phase trees, zero boundary and scope checks passed")


if __name__ == "__main__":
    main()
