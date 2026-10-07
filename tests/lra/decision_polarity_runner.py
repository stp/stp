#!/usr/bin/env python3
"""Require actual decision-time advice in the command-line solver."""

import subprocess
import sys
from persistent_session_runner import run


SOURCE = """
(set-logic QF_LRA)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (>= x 1))
(assert (>= y 1))
(assert (or (< (+ x y) 5) (> (+ x y) 10)))
(check-sat)
(exit)
"""

# The first Boolean candidate conflicts with arithmetic; the later descent
# still has an ordinary decision to advise, with first-search left at default.
LATE_SOURCE = """
(set-logic QF_LRA)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (>= x 1))
(assert (>= y 1))
(assert (or (< (+ x y) 1) (> (+ x y) 10)))
(assert (or (< (- x y) 1) (> (- x y) 5)))
(check-sat)
(exit)
"""


# Both instances above are built against a backend whose decisions default
# to true, as CaDiCaL's do: LATE_SOURCE's first Boolean candidate is then
# infeasible, so the theory joins the search, and the advice disagrees with
# the phase it is offered. MiniSat's decisions default to false, under which
# neither holds -- that candidate is feasible, and the advice agrees -- so it
# is given the mirror images.

# Every atom holds at the bounds, where the tableau starts: whatever a
# decision defaulting to false picks, the advice turns it around.
FALSE_SOURCE = """
(set-logic QF_LRA)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (>= x 1))
(assert (>= y 1))
(assert (or (< (+ x y) 5) (< (- x y) 7)))
(check-sat)
(exit)
"""

# The first row pins x and y together, so (>= x 2) and (>= y 2) agree in
# every model; a first candidate that decides either to false takes one
# without the other, which only the tableau can refute.
FALSE_LATE_SOURCE = """
(set-logic QF_LRA)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (>= (- x y) 0))
(assert (<= (- x y) 0))
(assert (or (>= x 2) (>= y 2)))
(assert (or (< (+ x y) 1) (> (+ x y) 3)))
(check-sat)
(exit)
"""

DEFAULTS_TO_FALSE = {"--minisat"}


def main():
    backend = sys.argv[2] if len(sys.argv) > 2 else "--cadical"
    first_source, late_source = ((FALSE_SOURCE, FALSE_LATE_SOURCE)
                                 if backend in DEFAULTS_TO_FALSE
                                 else (SOURCE, LATE_SOURCE))
    rejected = subprocess.run(
        [sys.argv[1], "--SMTLIB2", backend, "--lra-decision-polarity=1",
         "--lra-theory-propagation=0"],
        input=first_source, text=True, capture_output=True, timeout=30)
    assert rejected.returncode != 0, rejected.stdout
    assert "requires --lra-theory-propagation=1" in rejected.stderr, rejected.stderr
    for polarity in ([], ["--lra-decision-polarity=0"],
                     ["--lra-decision-polarity=1", "--lra-decision-polarity=0"]):
        flags = [backend, "--lra-theory-propagation=0", *polarity]
        answers, metrics = run(sys.argv[1], first_source, flags)
        assert answers == ["sat"], (flags, answers)
        assert metrics and all(not m["failure"] for m in metrics), flags
        assert all(m["polarity_enabled"] == 0 for m in metrics), flags
        assert all(m["polarity_queries"] == 0 for m in metrics), flags
    for floating in (0, 1):
        for first in (0, 1):
            for setting in (None, 0, 1):
                enabled = 1 if setting is None else setting
                flags = [backend, f"--lra-float-driver={floating}"]
                if first:
                    flags.append("--lra-first-search=1")
                if setting is not None:
                    flags.append(f"--lra-decision-polarity={setting}")
                answers, metrics = run(sys.argv[1], first_source if first else late_source, flags)
                assert answers == ["sat"], (flags, answers)
                assert metrics and all(not m["failure"] for m in metrics), flags
                assert all(m["polarity_supported"] == 1 for m in metrics), flags
                assert all(m["polarity_enabled"] == enabled for m in metrics), flags
                assert sum(m["first_search_connections"] for m in metrics) == first, flags
                queries = sum(m["polarity_queries"] for m in metrics)
                if enabled:
                    assert queries > 0, flags
                    assert sum(m["polarity_advice"] for m in metrics) > 0, flags
                    assert sum(m["polarity_changes"] for m in metrics) > 0, flags
                    source = "polarity_float" if floating else "polarity_exact"
                    assert sum(m[source] for m in metrics) > 0, flags
                elif not enabled:
                    assert queries == 0, flags
    print(f"PASS decision polarity ({backend}): default/on/off, live advice, "
          "exact/float, first-search on/off, propagation disabled")


if __name__ == "__main__":
    main()
