#!/usr/bin/env python3
"""Public UF completion agrees with the combined scalar/Real model."""
import re
import subprocess
import sys


def expressions(text):
    tokens = iter(re.findall(r"\|[^|]*\||[()]|[^\s()]+", text))

    def read(token):
        if token != "(":
            return token
        value = []
        for token in tokens:
            if token == ")":
                return value
            value.append(read(token))
        raise AssertionError("unterminated model output")

    return [read(token) for token in tokens]


def check(solver, name, body, expected, flags):
    body = body.replace("\n", "\n(set-option :produce-models true)\n", 1)
    result = subprocess.run(
        [solver, "--SMTLIB2", *flags], input=body, text=True,
        capture_output=True, timeout=20)
    assert result.returncode == 0, (name, result.stdout, result.stderr)
    output = expressions(result.stdout)
    assert [x for x in output if isinstance(x, str)] == ["sat"] * len(expected), (
        name, result.stdout, result.stderr)
    values = [[pair[-1] for pair in x] for x in output if isinstance(x, list)]
    assert values == expected, (name, values, expected, result.stderr)


CASES = [
    ("bool", """(set-logic QF_UFLRA)
(declare-fun f (Bool) Real)
(declare-fun p () Bool)
(declare-fun q () Bool)
(assert p)
(assert (= p q))
(assert (= (f p) 3))
(assert (= (f false) 8))
(check-sat)
(get-value ((f q) (f (not q))))
""", [["3", "8"]]),
    ("uninterpreted-sort", """(set-logic QF_UFLRA)
(declare-sort S 0)
(declare-fun f (S) Real)
(declare-fun a () S)
(declare-fun b () S)
(declare-fun c () S)
(assert (= a b))
(assert (distinct a c))
(assert (= (f a) 5))
(assert (= (f c) 7))
(check-sat)
(get-value ((f b) (f (ite false b c))))
""", [["5", "7"]]),
    ("nested-real-domain", """(set-logic QF_UFLRA)
(declare-fun p (Real) Bool)
(declare-fun f (Bool) Real)
(declare-fun x () Real)
(assert (= x 0))
(assert (p 0))
(assert (= (f true) 1))
(assert (= (f false) 2))
(check-sat)
(get-value ((p 0) (p x) (p 1) (f (p 0)) (f (p x)) (f (p 1))))
""", [["true", "true", "false", "1", "1", "2"]]),
    ("constant-real-domain", """(set-logic QF_UFLRA)
(declare-fun p (Real) Bool)
(assert (p 0))
(check-sat)
(get-value ((p (+ 0 0)) (p 1)))
""", [["true", "false"]]),
    ("lifecycle", """(set-logic QF_UFLRA)
(declare-fun f (Bool) Real)
(declare-fun p () Bool)
(declare-fun q () Bool)
(assert (= p q))
(assert (= (f false) 3))
(assert (= (f true) 4))
(push 1)
(assert (not p))
(check-sat)
(get-value ((f q)))
(pop 1)
(push 1)
(assert p)
(check-sat)
(get-value ((f q)))
(pop 1)
(push 1)
(assert (not p))
(check-sat)
(get-value ((f q)))
(reset)
(set-logic QF_UFLRA)
(declare-fun f (Bool) Real)
(declare-fun q () Bool)
(assert q)
(assert (= (f true) 9))
(check-sat)
(get-value ((f q)))
""", [["3"], ["4"], ["3"], ["9"]]),
]


def main():
    for flags in ([], ["--uf-propagate-equalities=0"]):
        for name, body, expected in CASES:
            check(sys.argv[1], name, body, expected, flags)
    print("PASS mixed UF model: scalar sorts, nested applications, push/pop/reset")


if __name__ == "__main__":
    main()
