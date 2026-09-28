#!/usr/bin/env python3
"""Exact point oracle, recognition boundaries and query scoping for ReLUs."""
from fractions import Fraction
import random
import re
import subprocess
import sys


def rat(x):
    x = Fraction(x)
    s = f"(/ {abs(x.numerator)} {x.denominator})"
    return f"(- {s})" if x < 0 else s


def relu(pre, post, reverse=False, strict=False):
    le, ge = ("<", ">") if strict else ("<=", ">=")
    if reverse:
        return f"(or (and (= {pre} {post}) ({le} 0 {pre})) (and (= 0 {post}) ({ge} 0 {pre})))"
    return f"(or (and ({le} {pre} 0) (= {post} 0)) (and ({ge} {pre} 0) (= {post} {pre})))"


def source(assertions, symbols=("x", "y", "z", "a", "b")):
    return "(set-logic QF_LRA)\n" + "\n".join(
        f"(declare-fun {v} () Real)" for v in symbols) + "\n" + "\n".join(
        f"(assert {a})" for a in assertions) + "\n(check-sat)\n"


def run(solver, text, enabled=1, floating=1, extra=()):
    r = subprocess.run([solver, "--SMTLIB2", "-s", "--lra-verify-conflicts=1",
                        "--lra-relu-lp=off", "--lra-model-reconstruction=off",
                        "--lra-verify-canonical=1", f"--lra-relu-bounds={enabled}",
                        f"--lra-float-driver={floating}", *extra], input=text,
                       text=True, capture_output=True, timeout=30)
    assert r.returncode == 0, r.stderr[-5000:]
    return re.findall(r"^(sat|unsat|unknown)$", r.stdout, re.M), r.stderr


def main():
    solver = sys.argv[1]
    # An expired query must leave before ReLU construction and registration,
    # even when the unchecked input has a straightforward exact refutation.
    expired = subprocess.run(
        [solver, "--SMTLIB2", "-s", "--lra-relu-bounds=1", "--max-time=0"],
        input=source([relu("x", "y"), "(< y 0)"]) +
              "(get-info :reason-unknown)\n", text=True,
        capture_output=True, timeout=30)
    assert expired.returncode == 0, expired.stderr
    assert re.search(r"^unknown$", expired.stdout, re.M), expired.stdout
    assert ":reason-unknown timeout" in expired.stdout, expired.stdout
    assert "LRA ReLU:" not in expired.stderr, expired.stderr
    rng = random.Random(74431)
    cases = []
    # Evaluate two affine/ReLU layers independently at pinned rational inputs.
    for i in range(48):
        x = Fraction(rng.randrange(-6, 7), 3)
        a = Fraction(rng.choice((-5, -2, 1, 3)), 7)
        c = Fraction(rng.randrange(-2, 3), 11)
        y = max(a*x + c, 0)
        z = max(Fraction(2, 3)*y - Fraction(1, 7), 0)
        expected = z + (Fraction(1, 13) if i % 3 == 0 else 0)
        assertions = [f"(= x {rat(x)})", f"(= a (+ (* {rat(a)} x) {rat(c)}))",
                      relu("a", "y", i % 2 == 0),
                      "(= b (- (* (/ 2 3) y) (/ 1 7)))", relu("b", "z"),
                      f"(= z {rat(expected)})"]
        rng.shuffle(assertions)  # affected queue must not depend on source order
        cases.append((source(assertions), "sat" if expected == z else "unsat"))
    # Unbounded inputs, zero boundary, backward output bounds, and strict input.
    cases += [(source(a), expected) for a, expected in [
        ([relu("x", "y"), "(< y 0)"], "unsat"),
        ([relu("x", "y"), "(= y 0)", "(< x 0)"], "sat"),
        ([relu("x", "y"), "(= x 0)", "(= y 0)"], "sat"),
        ([relu("x", "y"), "(> y 1)", "(<= x 1)"], "unsat"),
        ([relu("x", "y"), "(< x 0)", "(> y 0)"], "unsat"),
        ([relu("x", "y", strict=True), "(= x 0)"], "unsat"),
        (["(or (and (<= x 0) (= y 0)) (and (>= x 0) (= y (+ x 1))))",
          "(= x 1)", "(= y 2)"], "sat"),
        ([f"(or {relu('x', 'y')} (= y (- 1)))", "(= y (- 1))"], "sat"),
    ]]
    for floating in (0, 1):
        for enabled in (0, 1):
            for text, answer in cases:
                actual, log = run(solver, text, enabled, floating)
                assert actual == [answer], (text, actual, answer, log[-3000:])

    # A reversed chain requires repeated affected-definition propagation. Both
    # phases are proved, and this remains independent of the older bound pass.
    chain = source([relu("b", "z"), "(= b (- y 2))", relu("a", "y"),
                    "(= a (+ x 3))", "(>= x (- 2))", "(<= x (- 1))"])
    actual, log = run(solver, chain, extra=tuple(
        f"--lra-presolve-{s}=0" for s in
        ("subst", "rows", "bounds", "propagate", "unconstrained")))
    assert actual == ["sat"] and "relations=2, fixed=2" in log, log
    alias = source(["(= a x)", relu("a", "y"), "(>= x 1)", "(<= x 2)"])
    actual, log = run(solver, alias, extra=tuple(
        f"--lra-presolve-{s}=0" for s in
        ("subst", "rows", "bounds", "propagate", "unconstrained")))
    assert actual == ["sat"] and "relations=1, fixed=1" in log, log

    incremental = source([relu("x", "y")]).replace("(check-sat)", "") + """
(push 1)
(assert (<= x (- 1)))
(assert (> y 0))
(check-sat)
(pop 1)
(push 1)
(assert (= x 2))
(assert (= y 2))
(check-sat)
(pop 1)
(check-sat)
"""
    assert run(solver, incremental)[0] == ["unsat", "sat", "sat"]
    # Recognition must not erase an extra condition in either branch.
    near = source(["(or (and (<= x 0) (= y 0) (> z 0)) (and (>= x 0) (= y x)))",
                   "(= x (- 1))", "(= z 0)"])
    assert run(solver, near)[0] == ["unsat"]
    print(f"ReLU bounds: {len(cases)*4} point/bound checks, queue and scope checks passed")


if __name__ == "__main__":
    main()
