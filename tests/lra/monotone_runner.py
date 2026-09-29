#!/usr/bin/env python3
"""Check reconstructed values against the input, through both LRA drivers."""
from fractions import Fraction
from pathlib import Path
import re
import subprocess
import sys

from mixed_uf_model_runner import expressions

NO_PRESOLVE = tuple(f"--lra-presolve-{stage}=0" for stage in
                    ("subst", "rows", "bounds", "propagate", "unconstrained"))


def evaluate(term, values):
    if isinstance(term, str):
        if term in values:
            return values[term]
        if term in ("true", "false"):
            return term == "true"
        return Fraction(term)
    op, *args = term
    args = [evaluate(arg, values) for arg in args]
    if op == "+":
        return sum(args)
    if op == "-":
        return -args[0] if len(args) == 1 else args[0] - sum(args[1:])
    if op == "*":
        return args[0] * args[1]
    if op == "/":
        return args[0] / args[1]
    if op == "not":
        return not args[0]
    if op == "and":
        return all(args)
    if op == "or":
        return any(args)
    if op == "=>":
        return not args[0] or args[1]
    if op == "ite":
        return args[1] if args[0] else args[2]
    if op == "distinct":
        return len(set(args)) == len(args)
    return {"<": lambda a, b: a < b, "<=": lambda a, b: a <= b,
            ">": lambda a, b: a > b, ">=": lambda a, b: a >= b,
            "=": lambda a, b: a == b}[op](*args)


def run(solver, text, flags):
    result = subprocess.run(
        [solver, "--SMTLIB2", *filter(None, sys.argv[2:]), "-s", "--lra-verify-conflicts=1",
         "--lra-verify-canonical=1", "--lra-relu-bounds=off",
         "--lra-relu-lp=off", *flags], input=text, text=True,
        capture_output=True, timeout=20)
    assert result.returncode == 0, (result.stdout, result.stderr)
    assert not re.search(r"^unknown$", result.stdout, re.M), result.stderr
    # -s also prints frontend progress and SAT comments on stdout, and
    # MiniSat frames its search statistics in rows of "=" and "|".
    output = "\n".join(line for line in result.stdout.splitlines()
                       if not line.startswith(("[", "c "))
                       and not re.match(r"([=|]).*\1$", line))
    return expressions(output), result.stderr


PREFIX = """(set-logic QF_LRA)
(set-option :produce-models true)
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(declare-const b Bool)
"""

DEFINITION_CASE = ["(= y (+ x 1))", "(= z (+ y 2))", "(> x 0)", "(> x 2)"]
LOCAL_OPAQUE_CASE = ["(> x 1)", "(> x 2)", "(<= (ite b y z) 10)"]
BLOCKED_OPAQUE_CASE = ["(> x 1)", "(> x 2)", "(<= (+ x (ite b y z)) 10)"]

CASES = [
    # Strict and closed extrema, arbitrary signs/scales and both directions.
    ["(>= x (+ y 1))", "(> x (+ z 2))", "(= y (/ 1 3))", "(= z (/ 2 3))"],
    ["(< (* (- (/ 2 3)) x) y)", "(>= (* 3 x) z)", "(= y 5)", "(= z 8)"],
    ["(< x y)", "(<= (* 2 x) z)", "(= y (- 4))", "(= z (- 11))"],
    ["(not (<= (* (- 2) x) y))", "(not (>= x z))", "(= y 3)", "(= z 1)"],
    # Successive eliminations and a formula reduced entirely to true.
    ["(< z x)", "(< (+ x 5) y)", "(< (+ x 10) y)"],
    ["(or (not (not (> x y))) b)", "(=> b (>= x z))", "(= y 0)", "(= z 2)"],
    # Shared atom at both polarities, equality and opposing directions.
    ["(or (< x 1) b)", "(or (not (< x 1)) (not b))", "(> x 0)"],
    ["(= x y)", "(> x 1)", "(< y 3)"],
    ["(> x 0)", "(< x (/ 1 1000000000000))"],
    # Unsupported arithmetic ITE cannot hide an occurrence of x.
    ["(< (ite b x y) z)", "(> x 2)", "(= y 1)", "(= z 2)"],
    # Ordinary affine removal after the new pass supplies its dependencies.
    ["(> x y)", "(> x (+ y 1))", "(= y (+ z 2))", "(= z 1)"],
    # Cancelled occurrences must not create a cycle in later affine replay.
    ["(> x y)", "(= y (- x x))"],
    ["(> x y)", "(= y (- (* 2 x) (+ x x)))"],
    ["(> x y)", "(= y (+ x (- x) 1))"],
    # Dead affine definitions must move out before monotone analysis, even
    # with optional replay off; their published values still follow x.
    DEFINITION_CASE,
    LOCAL_OPAQUE_CASE,
    BLOCKED_OPAQUE_CASE,
    ["(distinct x y)", "(> x 2)", "(> z 1)", "(> z 2)"],
]


def main():
    solver = sys.argv[1]
    for driver in (0, 1):
        for stages in ((), NO_PRESOLVE):
            for replay in ("off", "on"):
                flags = (*stages, f"--lra-float-driver={driver}",
                         f"--lra-model-reconstruction={replay}",
                         "--lra-presolve-monotone=1")
                for assertions in CASES:
                    text = PREFIX + "\n".join(f"(assert {a})" for a in assertions)
                    output, log = run(solver, text + "\n(check-sat)\n(get-value (x y z b))", flags)
                    assert output[0] == "sat", (assertions, output, log)
                    values = {key.strip("|"): evaluate(value, {}) for key, value in output[1]}
                    assert all(evaluate(expressions(a)[0], values) for a in assertions), (
                        assertions, values, log)
                    if assertions == DEFINITION_CASE or (
                            assertions == LOCAL_OPAQUE_CASE and stages == NO_PRESOLVE):
                        assert "LRA monotone: variables=1, atoms=2" in log, log
                    if assertions == BLOCKED_OPAQUE_CASE and stages == NO_PRESOLVE:
                        assert "LRA monotone: variables=0, atoms=0" in log, log
        flags = (*NO_PRESOLVE, f"--lra-float-driver={driver}", "--lra-presolve-monotone=1")
        lifecycle = PREFIX + """
(assert (> x (+ y 1)))
(assert (> x (+ z 2)))
(check-sat)
(push 1)
(assert (<= x (+ y 1)))
(check-sat)
(pop 1)
(check-sat)
"""
        output, _ = run(solver, lifecycle, flags)
        assert output == ["sat", "unsat", "sat"], output
        refused = PREFIX + "(assert (> x 1))\n(assert (> x 2))\n(check-sat)"
        output, log = run(solver, refused, (*flags, "--lra-presolve-monotone-work=1"))
        assert output == ["sat"] and "LRA monotone: variables=0, atoms=0" in log, log
        # Retain the known guard against arbitrarily valuing UF result scalars.
        uf = Path(__file__).parent.parent / "query-files/lra-presolve-unconstrained-uf-result.smt2"
        output, log = run(solver, uf.read_text(), flags)
        assert output == ["sat"], (output, log)
        assert "LRA monotone: variables=0, atoms=0" in log, log

        # A shared arithmetic DAG must be walked by nodes, not its paths.
        term = "(and (> t35 y) (> t35 z) (= y 1) (= z 2))"
        for i in range(35, 0, -1):
            term = f"(let ((t{i} (+ t{i-1} t{i-1}))) {term})"
        output, log = run(solver, PREFIX + f"(assert (let ((t0 x)) {term}))\n(check-sat)", flags)
        assert output == ["sat"] and "LRA monotone: variables=1, atoms=2" in log, log
    print("PASS monotone models: exact/float, signs, strictness, Boolean DAGs, scope and UF guard")


if __name__ == "__main__":
    main()
