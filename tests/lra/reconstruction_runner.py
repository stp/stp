#!/usr/bin/env python3
"""Reconstruction preserves source models, strictness and query scope."""
import re
import subprocess
import sys
from relu_runner import source, relu

NO_PRESOLVE = tuple(f"--lra-presolve-{stage}=0" for stage in
                    ("subst", "rows", "bounds", "propagate", "unconstrained"))


def run(solver, text, enabled=1, extra=()):
    result = subprocess.run(
        [solver, "--SMTLIB2", "-s", "--lra-verify-conflicts=1",
         "--lra-relu-bounds=off", "--lra-relu-lp=off",
         f"--lra-model-reconstruction={enabled}", *extra],
        input=text, text=True, capture_output=True, timeout=40)
    assert result.returncode == 0, result.stderr[-5000:]
    answers = re.findall(r"^(sat|unsat|unknown)$", result.stdout, re.M)
    return answers, result.stdout.replace("|", ""), result.stderr


def main():
    solver = sys.argv[1]
    # Query the removed values, not just satisfiability of the reduced formula.
    n = 120
    chain = source(["(>= x0 1)", "(<= x0 2)"] +
                   [f"(= x{i} (+ x{i-1} 1))" for i in range(1, n+1)],
                   [f"x{i}" for i in range(n+1)])
    chain += f"(get-value ((- x{n} x0)))\n"
    for enabled in (0, 1):
        answer, out, log = run(solver, chain, enabled, NO_PRESOLVE)
        assert answer == ["sat"], log
        assert re.search(rf"\(- x{n} x0\) {n}\)", out), out
        if enabled:
            assert f"eliminated={n}," in log, log
    constant = source(["(= x (/ 1 3))", "(= y (+ x (/ 1 6)))", "(= z y)"])
    constant += "(get-value (x y z))\n"
    answer, out, log = run(solver, constant, extra=NO_PRESOLVE)
    assert answer == ["sat"] and "(/ 1 3)" in out and "(/ 1 2)" in out, (out, log)
    # An inconsistent cycle cannot be erased as unused definitions.
    cases = [
        (["(= x (+ y 1))", "(= y (+ z 1))", "(= z x)"], "unsat"),
        (["(= y (+ x 1))", "(= y (+ x 2))"], "unsat"),
        (["(= y (+ x 1))", "(= y (+ x 1))", "(< x 0)"], "sat"),
        (["(= x y)", "(= y z)", "(> x 0)", "(< z 0)"], "unsat"),
        (["(> x 0)", "(< x (/ 1 1000000000000))", "(= y (+ x 1))"], "sat"),
    ]
    for assertions, expected in cases:
        for extra in ((), NO_PRESOLVE):
            answer, _, log = run(solver, source(assertions), extra=extra)
            assert answer == [expected], (assertions, log)
    incremental = source(["(>= x 0)", "(<= x 1)", "(= y (+ x 1))"]).replace("(check-sat)", "")
    incremental += """
(check-sat)
(push 1)
(assert (< y 1))
(check-sat)
(pop 1)
(check-sat)
(get-value ((- y x)))
"""
    answer, out, log = run(solver, incremental)
    assert answer == ["sat", "unsat", "sat"] and "((- y x) 1)" in out, (out, log)
    if sys.argv[2] == "ON":
        graph = ["(>= x (- 1))", "(<= x 1)", "(= a x)", relu("a", "y"),
                 "(= z (+ y (/ 1 3)))"]
        query = source(graph + ["(or (> z 1) (< z 0))"])
        query += "(get-value ((- z y)))\n"
        answer, out, log = run(solver, query, extra=("--lra-relu-lp=1",))
        assert answer == ["sat"] and "witness=1" in log, (out, log)
        assert "((- z y) (/ 1 3))" in out, out
        branch = source(graph + ["(>= y (/ 1 2))"])
        answer, _, log = run(solver, branch, extra=("--lra-relu-branch=1",))
        assert answer == ["sat"] and "witness=1" in log, log
        # A floating endpoint at a strict boundary is not an exact witness.
        impossible = source(graph + ["(or (> z (/ 4 3)) (< z (/ 1 3)))"])
        assert run(solver, impossible, extra=("--lra-relu-lp=1",))[0] == ["unsat"]
        # A Boolean condition is checked by the combined coordinator. It may
        # not disappear merely because the Real graph admits a witness.
        mixed = query.replace("(set-logic QF_LRA)", "(set-logic QF_LRA)\n(declare-const p Bool)\n(assert p)")
        answer, _, log = run(solver, mixed, extra=("--lra-relu-lp=1",))
        assert answer == ["sat"] and "witness=1" not in log, log
        # An active UF view declines replay, asked for or not: the congruence
        # lemmas of later rounds constrain the rows a witness would settle.
        # HiGHS may still refute, but not answer with a model of its own.
        uf = source(["(= x (+ t 1))", "(= y (+ t 1))", "(< (f x) 0)",
                     "(> (f y) 1)"], ("x", "y", "t")).replace(
            "(set-logic QF_LRA)",
            "(set-logic QF_UFLRA)\n(declare-fun f (Real) Real)")
        for enabled in (0, 1):
            for flags in (("--lra-highs-lp=1",), ("--lra-highs-replay=1",)):
                answer, _, log = run(solver, uf, enabled, flags)
                assert answer == ["unsat"] and "witness=1" not in log, (flags, log)
        # A triangle-relaxation witness separates two identical ReLUs. Exact
        # forward replay makes their outputs equal. The screen must discard
        # this candidate without changing the final exact refutation.
        duplicate = source(["(>= x (- 1))", "(<= x 1)", relu("x", "y"),
                            relu("x", "z"),
                            "(or (>= (- y z) (/ 1 4)) (<= (- y z) (- (/ 1 4))))"])
        for screen in (0, 1):
            flags = ("--lra-relu-lp=1", "--lra-relu-branch=1", f"--lra-replay-screen={screen}")
            answer, _, log = run(solver, duplicate, extra=flags)
            assert answer == ["unsat"], log
            screened = re.findall(r"replay_screened=(\d+)", log)
            assert screened and (int(screened[0]) > 0) == bool(screen), log
            # Near-zero strict predicates and their negations remain eligible
            # for exact checking, even inside a Boolean conditional.
            near = source(graph + ["(or (not (<= z (/ 1 3))) (= x 0))"])
            assert run(solver, near, extra=flags)[0] == ["sat"]
    print("PASS exact reconstruction: dead definitions, models, cycles, strictness, scope and LP replay")


if __name__ == "__main__":
    main()
