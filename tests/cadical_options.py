"""Exercise CLI validation, actual backend values and incremental rebuilds."""

import os
from pathlib import Path
import re
import subprocess
import sys
import unittest

SOLVER = sys.argv.pop(1)
HAS_INPROBING = sys.argv.pop(1) == "1"
QUERIES = Path(__file__).with_name("query-files")
FORMULA = """(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(assert (= (bvmul x y) #x33))
(check-sat)
"""
TRIVIAL = "(set-logic QF_BV)\n(assert true)\n(check-sat)\n"
UNAVAILABLE = "is unavailable in this CaDiCaL build"


def has_efficiency_controls():
    """Whether this CaDiCaL knows elimmineff and elimmaxeff.

    Those are the 3.x names. 2.x has the same controls as elimineff and
    elimaxeff, and STP rejects its own options there rather than map them.
    """
    result = subprocess.run([SOLVER, "--SMTLIB2", "--cadical",
                             "--cadical-elimmineff=10000",
                             "--cadical-elimmaxeff=100000"],
                            input=TRIVIAL, text=True, capture_output=True,
                            timeout=90)
    return UNAVAILABLE not in result.stderr


HAS_EFFICIENCY_CONTROLS = has_efficiency_controls()
needs_efficiency_controls = unittest.skipUnless(
    HAS_EFFICIENCY_CONTROLS, "this CaDiCaL predates elimmineff/elimmaxeff")


class CadicalOptionsTests(unittest.TestCase):
    def run_solver(self, args, source=FORMULA, env=None):
        environment = {k: v for k, v in os.environ.items()
                       if not k.startswith("CADICAL_")}
        environment.update(env or {})
        return subprocess.run([SOLVER, "--SMTLIB2", *args], input=source,
                              text=True, capture_output=True, env=environment,
                              timeout=90)

    def check_settings(self, args, expected, env=None, source=FORMULA):
        result = self.run_solver(["--cadical", "-s", *args], source, env)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        settings = re.findall(r"CaDiCaL elimination: elim=(\d+) "
                              r"elimmineff=(\d+) elimmaxeff=(\d+)", result.stderr)
        self.assertTrue(settings, result.stdout + result.stderr)
        self.assertTrue(all(tuple(map(int, values)) == expected for values in settings),
                        settings)
        return result

    @needs_efficiency_controls
    def test_explicit_values_override_environment_and_search_bias(self):
        for elim in (0, 1):
            for bias in ("none", "sat", "unsat"):
                with self.subTest(elim=elim, bias=bias):
                    result = self.check_settings(
                        ["--disable-simplifications", f"--cadical-elim={elim}",
                         "--cadical-elimmineff=10000",
                         "--cadical-elimmaxeff=100000", f"--search-bias={bias}"],
                        (elim, 10000, 100000),
                        {"CADICAL_ELIM": str(1 - elim), "CADICAL_ELIMMINEFF": "23",
                         "CADICAL_ELIMMAXEFF": "47"})
                    self.assertEqual(re.findall(r"^(?:sat|unsat|unknown)$", result.stdout,
                                                re.MULTILINE), ["sat"])

    @needs_efficiency_controls
    def test_unspecified_options_retain_environment(self):
        env = {"CADICAL_ELIM": "0", "CADICAL_ELIMMINEFF": "23",
               "CADICAL_ELIMMAXEFF": "47"}
        self.check_settings(["--disable-simplifications"], (0, 23, 47), env)
        self.check_settings(["--disable-simplifications", "--cadical-elimmaxeff=100000"],
                            (0, 23, 100000), env)

    def test_bad_values_fail_even_without_sat_search(self):
        for option in ("--cadical-elim", "--cadical-elim=-1", "--cadical-elim=2",
                       "--cadical-elim=bogus",
                       "--cadical-elimmineff=-1", "--cadical-elimmaxeff=-1",
                       "--cadical-elimmineff=2147483647", "--cadical-elimmaxeff=2147483647",
                       "--cadical-elimmaxeff=999999999999999999999999"):
            with self.subTest(option=option):
                result = self.run_solver(["--cadical", option], TRIVIAL)
                self.assertGreater(result.returncode, 0, result.stdout + result.stderr)
                self.assertIn(option.split("=")[0], result.stderr)
                self.assertNotIn("terminate called", result.stderr)
                self.assertNotRegex(result.stdout, r"(?m)^(sat|unsat|unknown)$")

    def test_older_backend_declines_efficiency_controls(self):
        if HAS_EFFICIENCY_CONTROLS:
            self.skipTest("this CaDiCaL has elimmineff/elimmaxeff")
        for option in ("--cadical-elimmineff=10000", "--cadical-elimmaxeff=100000"):
            with self.subTest(option=option):
                result = self.run_solver(["--cadical", option], TRIVIAL)
                self.assertGreater(result.returncode, 0, result.stdout + result.stderr)
                self.assertIn(option.split("=")[0] + " " + UNAVAILABLE, result.stderr)
                self.assertNotRegex(result.stdout, r"(?m)^(sat|unsat|unknown)$")
        # The elimination switch itself is common to both lines.
        result = self.run_solver(["--cadical", "-s", "--disable-simplifications",
                                  "--cadical-elim=0"])
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("CaDiCaL elimination: elim=0 elimmineff=unavailable "
                      "elimmaxeff=unavailable", result.stderr)
        self.assertEqual(re.findall(r"^(?:sat|unsat|unknown)$", result.stdout,
                                    re.MULTILINE), ["sat"])

    def test_other_backend_rejects_explicit_controls(self):
        help_text = self.run_solver(["--help"], "").stdout
        backend = next((name for name in ("--minisat", "--cryptominisat")
                        if name in help_text), None)
        if backend is None:
            self.skipTest("no second backend compiled in")
        result = self.run_solver([backend, "--cadical-elim=0"], TRIVIAL)
        self.assertGreater(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("require the CaDiCaL backend", result.stderr)
        self.assertNotRegex(result.stdout, r"(?m)^(sat|unsat|unknown)$")

    @needs_efficiency_controls
    def test_incremental_relief_rebuild_retains_options_and_answers(self):
        source = (QUERIES / "incremental-tests/reencode-relief.smt2").read_text()
        for elim in (0, 1):
            with self.subTest(elim=elim):
                result = self.check_settings(
                    ["--incremental", "--incremental-reencode-limit=60",
                     f"--cadical-elim={elim}", "--cadical-elimmineff=10000",
                     "--cadical-elimmaxeff=100000"], (elim, 10000, 100000), source=source)
                self.assertIn("re-encoded from scratch", result.stderr)
                self.assertEqual(re.findall(r"^(?:sat|unsat|unknown)$", result.stdout,
                                            re.MULTILINE), ["sat"] * 12 + ["unsat", "sat"])

    @needs_efficiency_controls
    def test_incremental_retirement_honours_explicit_enable(self):
        if not HAS_INPROBING:
            self.skipTest("backend cannot retire inprobing")
        source = FORMULA.replace("(check-sat)", "(check-sat)\n(check-sat)")
        result = self.check_settings(
            ["--incremental", "--incremental-inprobing=off", "--cadical-elim=1",
             "--cadical-elimmineff=10000", "--cadical-elimmaxeff=100000"],
            (1, 10000, 100000), source=source)
        self.assertIn("inprobing retired", result.stderr)
        self.assertEqual(re.findall(r"^(?:sat|unsat|unknown)$", result.stdout,
                                    re.MULTILINE), ["sat", "sat"])

    @needs_efficiency_controls
    def test_exact_arithmetic_uses_explicit_controls(self):
        source = """(set-logic QF_LRA)
(declare-fun x () Real)
(assert (or (< x 0.0) (> x 2.0)))
(assert (<= x 1.0))
(assert (>= x (- 1.0)))
(check-sat)
"""
        result = self.check_settings(
            ["--lra-float-driver=0", "--cadical-elim=0",
             "--cadical-elimmineff=10000", "--cadical-elimmaxeff=100000"],
            (0, 10000, 100000), source=source)
        self.assertEqual(re.findall(r"^(?:sat|unsat|unknown)$", result.stdout,
                                    re.MULTILINE), ["sat"])


if __name__ == "__main__":
    unittest.main()
