#!/usr/bin/env python3
"""Run the branch-neutral QF_UFBV slice of peer regression suites.

The peer trees remain external inputs: this script deliberately selects only
ordinary sat/unsat queries whose semantics agree with UFSTP v2.  Parser-error,
lifecycle-policy, higher-order, unsupported-sort, and public-model tests are
left to the native v2 suite instead of importing a peer project's contract by
accident.
"""

import argparse
import json
import os
from pathlib import Path
import re
import shlex
import subprocess


VERDICT = re.compile(r"^(sat|unsat|unknown)$", re.MULTILINE)
NONZERO_DECL = re.compile(r"\(declare-fun\s+[^\s()]+\s*\(\s*[^)\s]")
UF_ARRAY_SIGNATURE = re.compile(
    r"\(declare-fun\s+[^\s()]+\s*\((?![\s)]*\)).*Array")
BOOL_ARRAY = re.compile(r"\(Array\s+Bool")
OUT_OF_FRAGMENT = re.compile(
    r"\b(forall|exists|declare-sort|define-sort|declare-datatype|"
    r"Int\b|Real\b|String\b|FloatingPoint|Float\d+|RoundingMode|"
    r"to_fp|bv2nat|nat2bv|int2bv|bv2int|ubv_to_int|sbv_to_int|"
    r"get-interpolant|par\s*\()")
LIFECYCLE_OR_MODEL = re.compile(
    r"\((?:reset(?:-assertions)?|get-model|get-value)\b|"
    r"\(set-option\s+:global-declarations\b")


def command(specification):
    argv = shlex.split(specification)
    if not argv:
        raise ValueError("empty solver command")
    return argv


def expected_verdicts(text):
    expected = re.findall(r";\s*EXPECT:\s*(sat|unsat)\b", text)
    if not expected:
        expected = re.findall(r":status\s+(sat|unsat)\b", text)
    return expected


def has_higher_order_use(text):
    function_names = re.findall(
        r"\(declare-fun\s+([^\s()]+)\s*\(\s*[^)\s]", text)
    for name in function_names:
        quoted = re.escape(name)
        if re.search(r"\(\s*=\s+" + quoted + r"[\s)]", text):
            return True
        if re.search(r"\(get-value\s*\(\s*" + quoted + r"[\s)]", text):
            return True
    return False


def classify(path, max_bytes):
    if path.stat().st_size > max_bytes:
        return None, "too-large"
    text = path.read_text(errors="replace")
    if not NONZERO_DECL.search(text):
        return None, "no-uf"
    logics = re.findall(r"\(set-logic\s+([A-Z_]+)\)", text)
    if logics and any(logic not in ("QF_UFBV", "QF_AUFBV")
                      for logic in logics):
        return None, "logic"
    if OUT_OF_FRAGMENT.search(text) or BOOL_ARRAY.search(text):
        return None, "unsupported-feature"
    if any(UF_ARRAY_SIGNATURE.search(line) for line in text.splitlines()):
        return None, "array-in-uf-signature"
    if LIFECYCLE_OR_MODEL.search(text):
        return None, "v2-policy-owned"
    if has_higher_order_use(text):
        return None, "higher-order"
    expected = expected_verdicts(text)
    if not expected or text.count("(check-sat") != len(expected):
        return None, "expectations"
    return (text, expected), None


def run(argv, text, timeout):
    process = subprocess.run(
        argv, input=text, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        text=True, timeout=timeout, check=False)
    return process.returncode, VERDICT.findall(process.stdout), process.stdout


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--stp", required=True)
    parser.add_argument(
        "--root", action="append", required=True,
        help="peer regression root (repeatable)")
    parser.add_argument(
        "--mode", action="append", choices=("batch", "persistent"),
        help="STP solve mode (repeatable; default: both)")
    parser.add_argument(
        "--arbiter",
        help="optional stdin solver command used to arbitrate mismatches")
    parser.add_argument("--max-bytes", type=int, default=100000)
    parser.add_argument("--timeout", type=float, default=120.0)
    parser.add_argument("--evidence-out")
    args = parser.parse_args()
    if args.max_bytes <= 0 or args.timeout <= 0:
        parser.error("--max-bytes and --timeout must be positive")

    modes = args.mode or ["batch", "persistent"]
    stp = command(args.stp)
    arbiter = command(args.arbiter) if args.arbiter else None
    selected = []
    skipped = {}
    for root_text in args.root:
        root = Path(os.path.expanduser(root_text))
        if not root.is_dir():
            parser.error("peer root is not a directory: %s" % root)
        for path in root.rglob("*.smt2"):
            item, reason = classify(path, args.max_bytes)
            if item is None:
                skipped[reason] = skipped.get(reason, 0) + 1
            else:
                selected.append((path, item[0], item[1]))

    failures = []
    runs = 0
    for path, source, expected in sorted(selected):
        for mode in modes:
            argv = stp + ["--SMTLIB2", "--uninterpreted-functions",
                          "--incremental=" + ("off" if mode == "batch"
                                               else "on")]
            returncode, observed, output = run(argv, source, args.timeout)
            runs += 1
            if returncode == 0 and observed == expected:
                continue
            arbitration = None
            if arbiter is not None:
                arbiter_rc, arbitration, arbiter_output = run(
                    arbiter, source, args.timeout)
                if arbiter_rc != 0:
                    arbitration = ["command-failed", arbiter_output[:400]]
            failures.append({
                "file": str(path),
                "mode": mode,
                "expected": expected,
                "observed": observed,
                "returncode": returncode,
                "arbiter": arbitration,
                "output": output[:1000],
            })

    evidence = {
        "schema": 1,
        "selected_files": len(selected),
        "solver_runs": runs,
        "modes": modes,
        "skipped_by_reason": dict(sorted(skipped.items())),
        "failures": failures,
        "result": "pass" if not failures else "fail",
    }
    encoded = json.dumps(evidence, indent=2, sort_keys=True) + "\n"
    if args.evidence_out:
        Path(args.evidence_out).write_text(encoded)
    print(encoded, end="")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
