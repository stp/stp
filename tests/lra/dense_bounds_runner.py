#!/usr/bin/env python3
"""Check bound-presolve semantics and arithmetic work on widening rows."""

from fractions import Fraction
import random
import re
import subprocess
import sys


def run(solver, source, bounds=1, floating=1):
    result = subprocess.run(
        [solver, "--SMTLIB2", "-s", "--lra-verify-conflicts=1",
         "--lra-verify-canonical=1", f"--lra-presolve-bounds={bounds}",
         f"--lra-float-driver={floating}",
         *[f"--lra-presolve-{stage}=0" for stage in
           ("subst", "rows", "propagate", "unconstrained")]],
        input=source, text=True, capture_output=True, timeout=60)
    assert result.returncode == 0, result.stderr[-4000:]
    answers = [l for l in result.stdout.splitlines()
               if l in ("sat", "unsat", "unknown", "unsupported")]
    return answers, result.stderr


def rational(value):
    value = Fraction(value)
    positive = f"(/ {abs(value.numerator)} {value.denominator})"
    return f"(- {positive})" if value < 0 else positive


def main():
    solver = sys.argv[1]
    # The guarded equality/inequality is outside the top-level unit bounds.
    # In particular, a target's own strict bound must not make its derived
    # opposite bound strict; another variable's strictness must survive.
    cases = [
        (["(> x 0)", "(>= y 0)", "(<= (+ x y) 1)",
          "(or (= x 1) p)", "(not p)"], "sat"),
        (["(>= x 0)", "(> y 0)", "(<= (+ x y) 1)",
          "(or (>= x 1) p)", "(not p)"], "unsat"),
        (["(> x 0)", "(> y 0)", "(<= (+ x y) 1)",
          "(or (= x (/ 1 2)) p)", "(not p)"], "sat"),
        (["(< x 0)", "(>= y 0)", "(<= (+ (- x) y) 1)",
          "(or (= x (- 1)) p)", "(not p)"], "sat"),
        (["(<= x 0)", "(> y 0)", "(<= (+ (- x) y) 1)",
          "(or (<= x (- 1)) p)", "(not p)"], "unsat"),
        (["(>= y 1)", "(<= y 2)", "(= z 1)", "(= (+ x y z) 3)",
          "(or (< x 0) p)", "(not p)"], "unsat"),
        (["(>= z 0)", "(<= z 1)", "(<= (+ x y z) 0)",
          "(or (= x 10) p)", "(not p)"], "sat"),
        (["(>= x 0)", "(>= y 0)", "(= (+ x y) 0)",
          "(or (> x 0) p)", "(not p)"], "unsat"),
        (["(<= x 0)", "(<= y 0)", "(<= z 0)", "(= (+ x y z) 0)",
          "(or (< x 0) p)", "(not p)"], "unsat"),
        (["(>= x 1)", "(<= y (- 2))",
          "(< (+ (* (/ 3 7) x) (* (- (/ 5 11)) y)) (/ 23 21))"], "unsat"),
        (["(>= y 0)", "(<= (+ x (- x) y) 1)",
          "(or (> x 1) p)", "(not p)"], "sat"),
    ]
    # Independent exact oracle: the Boolean guards force a known point.
    # Test all five relations, both coefficient signs, open bounds and
    # rational boundary cases without asking another solver for answers.
    rng = random.Random(4291)
    relations = ("<", "<=", "=", ">=", ">")
    for i in range(100):
        a = Fraction(rng.choice((-5, -3, 1, 7)), rng.choice((3, 7, 11)))
        b = Fraction(rng.choice((-7, -1, 3, 5)), rng.choice((3, 7, 11)))
        x = Fraction(rng.randrange(5), 2)
        y = Fraction(rng.randrange(-4, 5), 2)
        value = a*x + b*y
        rhs = value + rng.choice((-1, 0, 0, 1))
        relation = relations[i % len(relations)]
        holds = {"<": value < rhs, "<=": value <= rhs, "=": value == rhs,
                 ">=": value >= rhs, ">": value > rhs}[relation]
        strict = i % 2 == 0
        holds = holds and (x > 0 if strict else x >= 0)
        cases.append(([
            f"({'>' if strict else '>='} x 0)", "(<= x 2)",
            "(>= y (- 2))", "(<= y 2)",
            f"({relation} (+ (* {rational(a)} x) (* {rational(b)} y)) {rational(rhs)})",
            f"(or (= x {rational(x)}) p)", f"(or (= y {rational(y)}) p)",
            "(not p)"], "sat" if holds else "unsat"))
    source = """
(set-logic QF_LRA)
(declare-const x Real) (declare-const y Real) (declare-const z Real)
(declare-const p Bool)
"""
    for assertions, _ in cases:
        source += "(push 1)\n" + "\n".join(f"(assert {a})" for a in assertions)
        source += "\n(check-sat)\n(pop 1)\n"
    for floating in (0, 1):
        for bounds in (0, 1):
            answers, _ = run(solver, source, bounds, floating)
            expected = [answer for _, answer in cases]
            assert answers == expected, (floating, bounds, answers, expected)

    # Count actual exact-number arithmetic, not wall time or a counter
    # maintained by the row loop. Quadrupling row width should no longer
    # square the work. A generous ratio allows fixed parser/rewrite costs.
    work = []
    for width in (32, 128, 512):
        source = "(set-logic QF_LRA)\n"
        for i in range(width):
            source += f"(declare-const x{i} Real) (assert (>= x{i} 1)) (assert (<= x{i} 2))\n"
        terms = " ".join(f"x{i}" for i in range(width))
        source += f"(assert (<= (+ {terms}) {3*width}))\n(check-sat)\n"
        answers, diagnostics = run(solver, source)
        assert answers == ["sat"], answers
        counts = re.findall(r"bounds_ops=(\d+)", diagnostics)
        assert len(counts) == 1, diagnostics
        work.append(int(counts[0]))
    assert all(0 < b < 6*a for a, b in zip(work, work[1:])), work
    print(f"PASS dense bounds: {len(cases)} queries x 4 configurations; "
          f"widths 32/128/512 use {work} arithmetic operations")


if __name__ == "__main__":
    main()
