#!/usr/bin/env python3
"""Shared affine terms retain their DAG complexity through both solve paths."""
import json
import re
import subprocess
import sys


def main():
    depth = 40
    predicate = f"(> t{depth} 0)"
    for i in range(depth, 0, -1):
        predicate = f"(let ((t{i} (+ t{i-1} t{i-1}))) {predicate})"
    text = f"""(set-logic QF_LRA)
(declare-fun x () Real)
(assert (let ((t0 x)) {predicate}))
(check-sat)
(push 1)
(assert (<= x 0))
(check-sat)
(pop 1)
(check-sat)
"""
    for presolve in (True, False):
        flags = [] if presolve else [
            f"--lra-presolve-{stage}=0" for stage in
            ("subst", "rows", "bounds", "propagate", "unconstrained")]
        result = subprocess.run(
            [sys.argv[1], "--SMTLIB2", "-s", *flags], input=text,
            text=True, capture_output=True, timeout=20)
        assert result.returncode == 0, result.stderr
        assert re.findall(r"^(sat|unsat|unknown)$", result.stdout, re.M) == [
            "sat", "unsat", "sat"], (result.stdout, result.stderr)
        metrics = [json.loads(line[len("LRA-METRICS "):])
                   for line in result.stderr.splitlines()
                   if line.startswith("LRA-METRICS ")]
        assert metrics, result.stderr
        assert all(m["normalization_nodes"] <= 8 * (depth + 1)
                   for m in metrics), metrics
    print("PASS shared affine DAG: default presolve, direct normalization, push/pop")


if __name__ == "__main__":
    main()
