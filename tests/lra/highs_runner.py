#!/usr/bin/env python3
"""General HiGHS proposals: exact acceptance, refusal and assertion scoping."""
import re
import itertools
import random
from fractions import Fraction
import subprocess
import sys
from relu_runner import source, rat


def run(solver, text, flags=(), defaults=False):
    isolated = [] if defaults else ["--lra-highs-lp=1", "--lra-highs-mip=0"]
    result = subprocess.run([solver, "--SMTLIB2", "-s", "--max-time=15",
                             "--lra-verify-conflicts=1", *isolated, *flags],
                            input=text, text=True, capture_output=True, timeout=25)
    assert result.returncode == 0, result.stderr[-4000:]
    return re.findall(r"^(sat|unsat|unknown)$", result.stdout, re.M), result.stderr, result.stdout


def counter(log, name):
    match = re.search(r"\b" + re.escape(name) + r"=(\d+)", log)
    return int(match.group(1)) if match else 0


def test_defaults(solver, have_highs):
    binary = "(or (= b 0) (= b 1))"
    query = source([binary, "(>= b (/ 1 2))", "(= (* 7 x) b)"]) + "(get-value (b x))\n"
    # MIP is OFF by default (it paid for itself nowhere measured; see
    # UserDefinedFlags lra_highs_mip). A plain default run must do no HiGHS
    # work, regardless of whether the build has HiGHS compiled in.
    actual, log, output = run(solver, query, defaults=True)
    assert actual == ["sat"] and "(/ 1 7)" in output, (actual, log, output)
    assert "LRA HiGHS:" not in log, log
    # Explicitly off behaves identically.
    actual, log, _ = run(solver, query, ("--lra-highs-mip=0",), defaults=True)
    assert actual == ["sat"] and "LRA HiGHS:" not in log, log
    if not have_highs:
        # With no HiGHS compiled in, asking for MIP is refused.
        p = subprocess.run([solver, "--SMTLIB2", "--lra-highs-mip=1"],
                           input=query, capture_output=True, text=True, timeout=10)
        assert p.returncode != 0 and "ENABLE_HIGHS=ON" in p.stderr, p.stderr
        print("HiGHS-free default-off and explicit unsupported-option checks passed")
        return

    # The MIP machinery below is exercised by asking for it explicitly with
    # --lra-highs-mip=1, since it is off by default.
    mip = ("--lra-highs-mip=1",)
    actual, log, output = run(solver, query, mip, defaults=True)
    assert actual == ["sat"] and "(/ 1 7)" in output, (actual, log, output)
    assert counter(log, "mip_models") == 1 and counter(log, "mip_calls") == 1, log
    # Rejected domains must bypass numerical solving and the model-recovery
    # setup. The inspection itself must never imply integrality or a verdict.
    for assertions in [
        ["(= (* 3 x) 1)"],
        ["(>= b 0)", "(<= b 1)", "(= b (/ 1 2))"],
        ["(or (= b 1) (= b 2))", "(= b 2)"],
        ["(or (= b 0) (= b 1) (= b 2))", "(= b 2)"],
        ["(or (= b 0) (= x 1))", "(= b 2)", "(= x 1)"],
        ["(or (and " + binary + " (= x 0)) (= b 2))", "(= b 2)"],
    ]:
        actual, log, _ = run(solver, source(assertions), mip, defaults=True)
        assert actual == ["sat"] and "LRA HiGHS:" not in log, (assertions, actual, log)
    actual, log, _ = run(solver, query, ("--lra-highs-mip=1", "--lra-highs-seconds=0"), defaults=True)
    assert actual == ["sat"] and "LRA HiGHS:" not in log, log
    scaled = query.replace(binary, "(or (= (* 2 b) 0) (= 3 (* 3 b)))")
    assert counter(run(solver, scaled, mip, defaults=True)[1], "mip_models") == 1
    # Explicit LP remains available for continuous formulas.
    actual, log, _ = run(solver, source(["(= (* 3 x) 1)"]),
                         ("--lra-highs-lp=1",), defaults=True)
    assert actual == ["sat"] and counter(log, "models") == 1, log
    text = source(["(>= b (/ 1 2))", "(<= b 1)"]).replace("(check-sat)", "")
    text += "(push 1)\n(assert " + binary + ")\n(check-sat)\n(pop 1)\n(assert (= b (/ 3 4)))\n(check-sat)\n"
    actual, log, _ = run(solver, text, mip, defaults=True)
    assert actual == ["sat", "sat"] and log.count("LRA HiGHS:") == 1, log
    assert counter(log, "mip_models") == 1, log
    print("MIP default-off, explicit-MIP exact models, opt-out, eligibility, explicit LP and popped domains passed")


def test_mip(solver):
    binary = "(or (= b 0) (= 1 b))"
    flags = ("--lra-highs-mip=1", "--lra-highs-lp=0")
    # The relaxation selects a fractional endpoint; MIP must find b=1 and
    # recover the rational continuous coordinate in a fresh original-row LP.
    assertions = [binary, "(>= b (/ 1 2))", "(= (* 7 x) b)",
                  "(= (+ (* 2 x) (* 3 x)) (* 5 x))"]
    actual, log, output = run(solver, source(assertions) + "(get-value (b x))\n", flags)
    assert actual == ["sat"] and "mip_models=1" in log and "mip_calls=1" in log, log
    assert "(/ 1 7)" in output, output
    # Numerical integrality tolerance can report a solution to these close
    # rational equations. Exact recovery must reject that proposal.
    cases = [
        ([binary, "(= b 0.99999999999999999)"], "unsat", "mip_models=0"),
        ([binary, "(= b (/ 1 2))"], "unsat", "mip_models=0"),
        ([binary, "(< b 1)", "(> b 0)"], "unsat", "mip_models=0"),
        # An OR with a third option is not a binary domain.
        (["(or (= b 0) (= b 1) (= b 2))", "(= b 2)"], "sat", "binaries=0"),
        (["(or (and " + binary + " (= x 0)) (= b 2))", "(= b 2)"], "sat", "binaries=0"),
        # Bounds alone do not establish integrality of a Real variable.
        (["(>= b 0)", "(<= b 1)", "(= b (/ 1 2))"], "sat", "binaries=0"),
        # Duplicate values and different variables do not prove a domain.
        (["(or (= b 0) (= x 1))", "(= b 2)", "(= x 1)"], "sat", "binaries=0"),
    ]
    for assertions, expected, expected_counter in cases:
        actual, log, _ = run(solver, source(assertions), flags)
        name, value = expected_counter.split("=")
        assert actual == [expected] and counter(log, name) == int(value), (assertions, actual, log)
        assert run(solver, source(assertions), ("--lra-highs-mip=0",))[0] == [expected]
    text = source(["(>= b (/ 1 2))", "(<= b 1)"]).replace("(check-sat)", "")
    text += "(push 1)\n(assert " + binary + ")\n(check-sat)\n(pop 1)\n(assert (= b (/ 3 4)))\n(check-sat)\n"
    actual, log, _ = run(solver, text, flags)
    assert actual == ["sat", "sat"] and log.count("LRA HiGHS:") == 1, log
    actual, log, _ = run(solver, source([binary, "(>= b (/ 1 2))"]), flags + ("--lra-highs-seconds=0",))
    assert actual == ["sat"] and counter(log, "mip_calls") == 0, log
    print("HiGHS MIP exact recovery, domain recognition, rejected proposals and scoping passed")


def test_cuts(solver):
    # Two disjoint odd cycles have fractional packing value 5 but integer
    # value 4. HiGHS generates a root tableau cut; the callback recipe must
    # produce an exact split cut in STP, not just fall back to Boolean search.
    names = [f"b{i}" for i in range(10)]
    domains = [f"(or (= {b} 0) (= {b} 1))" for b in names]
    edges = [f"(<= (+ {names[j+i]} {names[j+(i+1)%5]}) 1)"
             for j in (0, 5) for i in range(5)]
    total = "(+ " + " ".join(names) + ")"
    flags = ("--lra-highs-cuts=1",)
    query = source(domains + edges + [f"(>= {total} 5)"], names)
    actual, log, _ = run(solver, query, flags)
    assert actual == ["unsat"], log
    assert re.search(r"recipe_callbacks=[1-9].*cuts=[1-9]", log), log
    # Replay must register the accepted root cuts as exact premises and close
    # the strengthened root with a checked LP conflict.
    actual, log, _ = run(solver, query, flags + ("--lra-highs-replay=1",))
    assert actual == ["unsat"] and "replay_refuted=1" in log, log
    assert re.search(r"cuts=[1-9].*replay_conflicts=[1-9]", log), log
    assert run(solver, source(domains + edges + [f"(>= {total} 4)"], names), flags)[0] == ["sat"]
    for limit in ("--lra-highs-cut-limit=0", "--lra-highs-seconds=0"):
        actual, log, _ = run(solver, query, flags + (limit,))
        assert actual == ["unsat"] and "cuts=0" in log, log
    # The integer proof is scoped to the explicit domains. After popping
    # them the very same constraints have a feasible fractional model.
    text = source(edges + [f"(>= {total} 5)"], names).replace("(check-sat)", "")
    text += "(push 1)\n" + "\n".join(f"(assert {d})" for d in domains)
    text += "\n(check-sat)\n(pop 1)\n(check-sat)\n"
    actual, log, _ = run(solver, text, flags)
    assert actual == ["unsat", "sat"] and "binaries=0" in log, log
    strict = source(["(or (= b 0) (= b 1))", "(> b 0)", "(< b 1)"])
    actual, log, _ = run(solver, strict, flags)
    assert actual == ["unsat"] and re.search(r"cuts=[1-9]", log), log
    print("HiGHS root recipe callback, exact split/rounding cuts, budgets and scope passed")


def test_replay(solver):
    binary = "(or (= b 0) (= b 1))"
    flags = ("--lra-highs-replay=1", "--lra-highs-lp=0")
    nested = source([binary, "(or (= a 0) (= a 1))", "(= (+ a b) (/ 1 2))"])
    actual, log, _ = run(solver, nested, flags)
    assert actual == ["unsat"] and "replay_refuted=1" in log, log
    assert re.search(r"replay_resolutions=[2-9]", log), log
    assert re.search(r"replay_screened=[1-9]", log), log
    # An unfinished sibling cannot be counted as refuted. Ordinary solving
    # is still allowed to finish this query, but replay must report it open.
    actual, log, _ = run(solver, nested, flags + ("--lra-highs-replay-nodes=1",))
    assert actual == ["unsat"] and "replay_refuted=0" in log and "replay_nodes=1" in log, log
    query = source([binary, "(>= b (/ 1 4))", "(= (* 7 x) b)"])
    actual, log, output = run(solver, query + "(get-value (b x))\n", flags)
    assert actual == ["sat"] and "replay_model=1" in log and "(/ 1 7)" in output, (log, output)
    # With just root+one child, retain the verified b!=0 clause and let the
    # coordinator finish the still-open tree. This also checks row-bound
    # explanations after backtracking from a column fixed at the wrong bit.
    actual, log, _ = run(solver, query, flags + ("--lra-highs-replay-nodes=2",))
    assert actual == ["sat"] and "replay_refuted=0" in log and "replay_model=0" in log, log
    assert "replay_clauses=1" in log and "replay_conflicts=1" in log, log
    for limit in ("--lra-highs-replay-nodes=0", "--lra-highs-seconds=0"):
        actual, log, _ = run(solver, query, flags + (limit,))
        assert actual == ["sat"] and "replay_nodes=0" in log, log
    text = source([binary]).replace("(check-sat)", "")
    text += "(push 1)\n(assert (= b (/ 1 2)))\n(check-sat)\n(pop 1)\n(assert (= b 0))\n(check-sat)\n"
    assert run(solver, text, flags)[0] == ["unsat", "sat"]
    # Retract the integrality premise itself. A previously learned integer
    # conflict must not exclude a feasible fractional Real assignment.
    text = source(["(= b (/ 1 2))"]).replace("(check-sat)", "")
    text += "(push 1)\n(assert " + binary + ")\n(check-sat)\n(pop 1)\n(check-sat)\n"
    assert run(solver, text, flags)[0] == ["unsat", "sat"]
    # A numerical failure on an open boundary is not an infeasible LP leaf.
    for assertions, expected in [([binary, "(> b 0)", "(< b 1)"], "unsat"),
                                  ([binary, "(> b 0)", "(<= b 1)"], "sat")]:
        assert run(solver, source(assertions), flags)[0] == [expected]
    # Independent finite-domain/interval oracle: enumerate the four binary
    # inputs and intersect exact intervals for the remaining continuous Real.
    rng = random.Random(88971)
    names = ["p", "q", "r", "t", "y"]
    for trial in range(32):
        rows = [([rng.randrange(-3, 4) for _ in range(4)], rng.randrange(-2, 3),
                 Fraction(rng.randrange(-9, 10), 3), (trial+i)%4 == 0) for i in range(4)]
        feasible = False
        for point in itertools.product((0, 1), repeat=4):
            lo, hi = Fraction(-1), Fraction(1)
            lo_open = hi_open = False
            possible = True
            for a, c, rhs, strict in rows:
                residual = rhs - sum(v*x for v, x in zip(a, point))
                if c == 0:
                    possible &= residual > 0 if strict else residual >= 0
                else:
                    bound = residual / c
                    if c > 0 and bound <= hi:
                        hi_open = strict or (bound == hi and hi_open)
                        hi = bound
                    if c < 0 and bound >= lo:
                        lo_open = strict or (bound == lo and lo_open)
                        lo = bound
            feasible |= possible and (lo < hi or (lo == hi and not lo_open and not hi_open))
        assertions = [f"(or (= {v} 0) (= {v} 1))" for v in names[:4]]
        assertions += ["(>= y (- 1))", "(<= y 1)"]
        for a, c, rhs, strict in rows:
            coefficients = a + [c]
            terms = [f"(* {rat(v)} {name})" for v, name in zip(coefficients, names) if v]
            lhs = "0" if not terms else terms[0] if len(terms) == 1 else "(+ " + " ".join(terms) + ")"
            assertions.append(f"({'<' if strict else '<='} {lhs} {rat(rhs)})")
        expected = ["sat" if feasible else "unsat"]
        for nodes in (2, 64):
            actual, log, _ = run(solver, source(assertions, names), flags + (f"--lra-highs-replay-nodes={nodes}",))
            assert actual == expected, (assertions, expected, actual, log)
    print("HiGHS binary replay: branch conflicts, coverage, partial clauses, models, retraction and 64 interval-oracle checks passed")


def main():
    solver, mode = sys.argv[1:3]
    if mode == "defaults":
        test_defaults(solver, sys.argv[3].upper() in ("ON", "TRUE", "1"))
        return
    if mode == "replay":
        test_replay(solver)
        return
    if mode == "cuts":
        test_cuts(solver)
        return
    if mode == "mip":
        test_mip(solver)
        return
    assert mode == "lp"
    cases = [
        (["(= (+ (* 3 x) y) 1)", "(= y 0)"], "sat", "models=1"),
        (["(= (+ x y z) 1)", "(= y 0)", "(= x 0)"], "sat", "models=1"),
        (["(<= (+ x y) 0)", "(>= (+ (* 2 x) (* 2 y)) 1)"], "unsat", "rays=1"),
        (["(= (+ x y) 0)", "(> x 0)", "(< x 1)"], "sat", "models=1"),
        (["(>= x 0)", "(< x 0)"], "unsat", None),
        (["(>= x 1)", "(>= y 1)", "(<= (+ x y) 1)"], "unsat", "rays=1"),
        (["(= x (/ 1 3))", "(= y (/ 1 7))", "(= (+ x y) (/ 10 21))"], "sat", "models=1"),
        # A tolerance-sized numerical inconsistency is still an exact conflict.
        (["(= x 1)", "(= x 1.00000000000000001)"], "unsat", None),
        # Conditional rows are not asserted to the LP, and a relaxation model
        # must satisfy every Boolean branch of the original source.
        (["(or (= x 1) (= x 2))", "(= x 3)"], "unsat", "models=0"),
        (["(= x 0)", "(not (= y 0))", "(= y 0)"], "unsat", "models=0"),
        (["(or (= x 1) (= x 2))", "(= x 2)"], "sat", "models=1"),
        (["(= x 0)", "(not (= y 0))"], "sat", "models=0"),
    ]
    for assertions, expected, counter in cases:
        actual, log, _ = run(solver, source(assertions))
        assert actual == [expected], (assertions, actual, log[-4000:])
        if counter:
            assert counter in log, log
        assert run(solver, source(assertions), ("--lra-highs-lp=0",))[0] == [expected]
    text = source(["(= (+ (* 3 x) y) 1)", "(= y 0)"]).replace("(check-sat)", "")
    text += "(check-sat)\n(get-value (x y))\n(push 1)\n(assert (>= x 1))\n(check-sat)\n(pop 1)\n(check-sat)\n(get-value (x y))\n"
    actual, log, output = run(solver, text)
    assert actual == ["sat", "unsat", "sat"], (actual, log)
    assert output.count("(/ 1 3)") == 2, output
    actual, log, _ = run(solver, source(["(= x (/ 1 3))"]), ("--lra-highs-seconds=0",))
    assert actual == ["sat"] and "lp_calls=0" in log, log
    print("HiGHS LP basis/ray certification, strictness, model and scope checks passed")


if __name__ == "__main__":
    main()
