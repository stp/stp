#!/usr/bin/env python3
"""Regression checks for the optional Satsuma pipeline; pass an STP binary."""
import itertools
import random
import subprocess
import sys

binary = sys.argv[1]
backend = sys.argv[2] if len(sys.argv) > 2 else "cadical"
assert backend in ("cadical", "cryptominisat", "kissat"), backend
cases = 0


def check(text, expected, extra=(), require_preprocessing=False):
    global cases
    cases += 1
    for mode in ("off", "lex", "fix"):
        proc = subprocess.run([binary, f"--{backend}", f"--satsuma={mode}",
                               "--check-sanity", "-s", *extra],
                              input=text, text=True, capture_output=True, timeout=30)
        answers = [line for line in proc.stdout.splitlines()
                   if line in ("sat", "unsat", "unknown")]
        assert proc.returncode == 0 and answers == expected, (mode, answers, proc.stderr)
        if require_preprocessing and mode != "off":
            assert f"satsuma: mode={mode}" in proc.stderr, proc.stderr
        if "--incremental=on" in extra and mode != "off":
            assert "satsuma: mode=" not in proc.stderr, proc.stderr
        if "--bv-term-abstraction=1" in extra and mode != "off":
            assert "satsuma: mode=" not in proc.stderr, proc.stderr
            assert "satsuma: skipped" in proc.stderr, proc.stderr
        if "--ackermanize" in extra and mode != "off":
            assert "satsuma: mode=" not in proc.stderr, proc.stderr
            assert "satsuma: skipped" in proc.stderr, proc.stderr
        if "--satsuma-input-limit=0" in extra and mode != "off":
            assert "satsuma: mode=" not in proc.stderr, proc.stderr
            assert "satsuma: skipped" in proc.stderr, proc.stderr


check("(set-logic QF_BV)(assert true)(check-sat)", ["sat"])
check("(set-logic QF_BV)(assert false)(check-sat)", ["unsat"])
check("""(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))(declare-fun y () (_ BitVec 8))
(assert (and (= (bvmul x y) #x06) (bvult x #x10) (bvult y #x10)))
(check-sat)""", ["sat"], require_preprocessing=True)

# Resource guards must preserve the ordinary CNF loader and reconstructed model.
bounded = """(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))(declare-fun y () (_ BitVec 8))
(assert (and (= (bvmul x y) #x06) (bvult x #x10) (bvult y #x10)))
(check-sat)"""
check(bounded, ["sat"], extra=("--satsuma-input-limit=0",))
if backend == "kissat":
    # Small array formulas are eagerly lowered to a complete batch CNF, but
    # their model registry still asks to freeze the original index bits.
    # One-shot Kissat must accept those requests without its incremental API.
    check("""(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun x () (_ BitVec 8))(declare-fun y () (_ BitVec 8))
(assert (= (select a x) x))(assert (= (select a y) y))
(assert (and (= (bvmul x y) #x06) (bvult x #x10) (bvult y #x10)))
(check-sat)""", ["sat"], extra=("--kissat-batch-only=true",),
          require_preprocessing=True)
for limit in (0, 1):
    check(bounded, ["sat"], extra=(f"--satsuma-iteration-limit={limit}",),
          require_preprocessing=True)

# Pigeonhole formulas exercise actual permutation symmetry, for both verdicts.
for pigeons, holes in ((4, 4), (5, 4), (6, 5)):
    declarations = [f"(declare-fun p{i}_{j} () Bool)"
                    for i in range(pigeons) for j in range(holes)]
    assertions = ["(assert (or " + " ".join(f"p{i}_{j}" for j in range(holes)) + "))"
                  for i in range(pigeons)]
    assertions += [f"(assert (or (not p{i}_{j}) (not p{k}_{j})))"
                   for j in range(holes) for i in range(pigeons) for k in range(i)]
    check("(set-logic QF_BV)" + "".join(declarations + assertions) + "(check-sat)",
          ["sat" if pigeons <= holes else "unsat"], require_preprocessing=True)

# Compare against an exhaustive oracle, including SAT model checking inside STP.
rng = random.Random(193)
for _ in range(40):
    clauses = [[rng.choice((-1, 1)) * rng.randrange(1, 7) for _ in range(3)]
               for _ in range(rng.randrange(8, 30))]
    satisfiable = any(all(any(values[abs(lit) - 1] == (lit > 0) for lit in clause)
                         for clause in clauses)
                      for values in itertools.product((False, True), repeat=6))
    declarations = "".join(f"(declare-fun p{i} () Bool)" for i in range(1, 7))
    assertions = "".join("(assert (or " + " ".join(
        f"p{lit}" if lit > 0 else f"(not p{-lit})" for lit in clause) + "))"
        for clause in clauses)
    check("(set-logic QF_BV)" + declarations + assertions + "(check-sat)",
          ["sat" if satisfiable else "unsat"])

check("""(set-logic QF_BV)(declare-fun x () (_ BitVec 8))
(assert (bvult x #x10))(check-sat)
(push 1)(assert (bvugt x #x80))(check-sat)(pop 1)(check-sat)""",
      ["sat", "unsat", "sat"], extra=("--incremental=on",))
check("""(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))(declare-fun y () (_ BitVec 8))
(assert (and (= (bvmul x y) #x06) (bvult x #x10) (bvult y #x10)))
(check-sat)""", ["sat"], extra=("--bv-term-abstraction=1",))
check("""(set-logic QF_BVFP)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(assert (fp.gt x (_ +zero 8 24)))
(assert (fp.lt y (_ +oo 8 24)))
(assert (fp.eq (fp.add RNE x y) ((_ to_fp 8 24) #x40400000)))
(check-sat)""", ["sat"], require_preprocessing=True)
check("""(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 66) (_ BitVec 8)))
(declare-fun i () (_ BitVec 66))
(assert (or (= a ((as const (Array (_ BitVec 66) (_ BitVec 8))) #x00))
            (= a ((as const (Array (_ BitVec 66) (_ BitVec 8))) #x01))))
(assert (bvugt (select a i) #x00))
(check-sat)""", ["sat"], extra=("--ackermanize", "--array-equality"))
print(f"{cases} cases passed with {backend} in off, lex, and fix modes; SAT models checked")
