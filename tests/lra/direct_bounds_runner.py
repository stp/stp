#!/usr/bin/env python3
"""Direct-bound controls: exact certificates, float mappings and query scope."""
import json
import sys
from fractions import Fraction
from monotone_runner import NO_PRESOLVE, PREFIX, evaluate, expressions, run


def metrics(log):
    return [json.loads(line.removeprefix("LRA-METRICS "))
            for line in log.splitlines() if line.startswith("LRA-METRICS ")]


def ordering_checks(solver):
    text = PREFIX + """
(assert (or b (<= (* 2 x) 6)))
(assert (or (not b) (<= x 5)))
(check-sat)
(push 1)
(assert (<= (* 2 x) 6))
(assert (not (<= x 5)))
(check-sat)
(pop 1)
(push 1)
(assert (= (* (- 3) x) (- 9)))
(check-sat)
(get-value (x))
(pop 1)
(check-sat-assuming ((not (>= (* (- 7) x) (- 35))) b))
(check-sat)
"""
    for mode in (0, 1, 2):
        for driver in (0, 1):
            for enabled in (0, 1):
                for persistent in (0, 1):
                    flags = (*NO_PRESOLVE, "--lra-presolve-monotone=0",
                             f"--lra-direct-bounds={mode}", f"--lra-float-driver={driver}",
                             f"--lra-singleton-ordering={enabled}",
                             f"--lra-persistent-state={persistent}",
                             "--incremental=" + ("on" if persistent else "off"))
                    output, log = run(solver, text, flags)
                    assert [x for x in output if isinstance(x, str)] == [
                        "sat", "unsat", "sat", "unsat", "sat"], (flags, output, log)
                    values = [x for x in output if isinstance(x, list)]
                    assert evaluate(values[0][0][1], {}) == 3, values
                    if persistent:
                        assert any(m["persistent_extensions"] > 0 for m in metrics(log)), log
                        # Persistent metrics are cumulative across extensions;
                        # isolate the first query for the clause-count check.
                        _, initial_log = run(solver, text.split("(push 1)")[0], flags)
                        assert metrics(initial_log)[0]["ordering_axioms"] == enabled, (
                            flags, initial_log)


def main():
    solver = sys.argv[1]
    ordering_checks(solver)
    cases = [
        ["(>= x 1)", "(<= x 2)", "(< (* (- 2) x) (- 2))"],
        ["(> (* (/ 2 3) x) (/ 1 3))", "(<= (* (/ 7 3) x) (/ 14 9))"],
        ["(<= (* (- 2) x) (- 2))", "(>= (* (- 3) x) (- 3))"],
        ["(not (>= (* (- 2) x) (- 2)))", "(<= x 2)"],
        ["(= (* (- 2) x) 3)", "(= (* 3 y) 2)", "(= (+ x y) (- (/ 5 6)))"],
        ["(<= x 1)", "(<= y 1)", "(> (+ x y) 1)", "(>= z (+ x y))"],
        ["(or (< (* (- 2) x) (- 3)) (> (* 3 x) 8))", "(<= x 2)"],
        # This coefficient cannot be represented by the advisory double tier.
        # Exact fallback still has to solve and publish the original equality.
        [f"(= (* {10**400} x) 1)"],
    ]
    impossible = [
        ["(<= (* 2 x) 2)", "(< (* (- 3) x) (- 3))"],
        ["(not (< (* (- 2) x) (- 2)))", "(> (* 3 x) 3)"],
        ["(<= x 1)", "(<= y 1)", "(> (+ x y) 2)"],
        ["(<= (* 2 x) 2)", "(>= (* (- 3) y) (- 3))", "(> (+ x y) 2)"],
        ["(= (* (- 2) x) 3)", "(>= (* 3 x) (- 4))"],
    ]
    for mode in (0, 1, 2):
        for driver in (0, 1):
            flags = (*NO_PRESOLVE, "--lra-presolve-monotone=0",
                     "--lra-model-reconstruction=off", f"--lra-float-driver={driver}",
                     f"--lra-direct-bounds={mode}")
            for assertions in cases:
                text = PREFIX + "\n".join(f"(assert {a})" for a in assertions)
                output, log = run(solver, text + "\n(check-sat)\n(get-value (x y z b))", flags)
                assert output[0] == "sat", (assertions, flags, output, log)
                values = {key.strip("|"): evaluate(value, {}) for key, value in output[1]}
                assert all(evaluate(expressions(a)[0], values) for a in assertions), (
                    assertions, flags, values, log)
                m = metrics(log)[-1]
                expected = (0 if mode == 0 else m["core_identity_rows"] if mode == 1
                            else m["core_singleton_rows"])
                assert m["core_direct_rows"] == expected, m
            for assertions in impossible:
                text = PREFIX + "\n".join(f"(assert {a})" for a in assertions)
                output, log = run(solver, text + "\n(check-sat)", flags)
                assert output == ["unsat"], (assertions, flags, output, log)

            lifecycle = PREFIX + """
(assert (>= x 1))
(assert (<= (* 2 x) 4))
(check-sat)
(push 1)
(assert (< (* (- 3) x) (- 6)))
(check-sat)
(pop 1)
(push 1)
(assert (= y (+ x 1)))
(check-sat)
(get-value ((- y x)))
(pop 1)
(check-sat-assuming ((> (* 2 x) 4)))
(check-sat)
(reset)
(set-logic QF_LRA)
(set-option :produce-models true)
(declare-const x Real)
(assert (= (* (- 2) x) 3))
(check-sat)
(get-value (x))
"""
            # Batch rebuilding and the optional persistent extension path.
            # Batch-only restart controls are covered by lra_core_direct-bounds.
            for persistent in (0, 1):
                output, log = run(solver, lifecycle, (*flags,
                    f"--lra-persistent-state={persistent}",
                    "--incremental=" + ("on" if persistent else "off")))
                answers = [x for x in output if isinstance(x, str)]
                assert answers == ["sat", "unsat", "sat", "unsat", "sat", "sat"], (
                    mode, driver, persistent, output, log)
                values = [x for x in output if isinstance(x, list)]
                assert evaluate(values[0][0][1], {}) == 1, values
                assert evaluate(values[1][0][1], {}) == -Fraction(3, 2), values
                if persistent:
                    assert any(m["persistent_extensions"] > 0 for m in metrics(log)), log
    print("PASS direct bounds: identity/scaled, exact/float, certificates, models, extension and reset")


if __name__ == "__main__":
    main()
