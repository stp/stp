#!/usr/bin/env python3
"""Deterministic benchmark-family runner for STP's UF implementation.

This is acceptance evidence, not a pass/fail micro-optimization target.  It
checks every answer while timing six core families -- durable traversal and
lowering, define-fun reuse, nested let, persistent identical-block reuse, pop
scope, and encoding-epoch rebuild -- in both fresh-query and persistent
exact-stack modes. It adds one family each for floating-point and
rounding-mode sorts, which do not scale like the bit-vector ones. Two fixed
scales make unexpected nonlinear regressions visible in the emitted JSON.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re
import statistics
import subprocess
import tempfile
import time


VERDICT = re.compile(r"^(sat|unsat|unknown)$", re.MULTILINE)


def header():
    return [
        "(set-logic QF_UFBV)",
        "(declare-fun f ((_ BitVec 16)) (_ BitVec 16))",
    ]


def bv(value):
    return "#x%04X" % (value & 0xFFFF)


def durable_traversal(size):
    lines = header()
    for index in range(size):
        lines.append("(assert (= (f %s) %s))" %
                     (bv(index), bv(index * 17 + 3)))
    lines += ["(check-sat)", "(exit)"]
    return "\n".join(lines) + "\n", ["sat"]


def define_fun_reuse(size):
    lines = header()
    lines.append(
        "(define-fun h ((z (_ BitVec 16))) (_ BitVec 16) "
        "(f (bvadd z #x0001)))")
    for index in range(size):
        # The second occurrence must reuse the specialized durable node.
        lines.append("(assert (= (h %s) (h %s)))" %
                     (bv(index), bv(index)))
        lines.append("(assert (= (h %s) %s))" %
                     (bv(index), bv(index * 13 + 5)))
    lines += ["(check-sat)", "(exit)"]
    return "\n".join(lines) + "\n", ["sat"]


def nested_let(size):
    lines = header()
    for index in range(size):
        value = bv(index)
        lines.append(
            "(assert (= (let ((a %s)) (let ((b a)) (let ((c b)) "
            "(f c)))) %s))" % (value, bv(index * 11 + 7)))
    lines += ["(check-sat)", "(exit)"]
    return "\n".join(lines) + "\n", ["sat"]


def identical_block_reuse(size):
    lines = header() + [
        "(declare-const x (_ BitVec 16))",
        "(assert (= (f x) #x0033))",
    ]
    lines += ["(check-sat)"] * size
    lines.append("(exit)")
    return "\n".join(lines) + "\n", ["sat"] * size


def pop_scope(size):
    cycles = max(2, size // 4)
    lines = header()
    for index in range(cycles):
        lines += [
            "(declare-const x%d (_ BitVec 16))" % index,
            "(declare-const y%d (_ BitVec 16))" % index,
        ]
    expected = []
    for index in range(cycles):
        lines += [
            "(push 1)",
            "(assert (= x%d y%d))" % (index, index),
            "(assert (distinct (f x%d) (f y%d)))" % (index, index),
            "(check-sat)",
            "(pop 1)",
            "(check-sat)",
        ]
        expected += ["unsat", "sat"]
    lines.append("(exit)")
    return "\n".join(lines) + "\n", expected


def epoch_rebuild(size):
    churn = max(4, size // 2)
    lines = header() + [
        "(declare-const base (_ BitVec 16))",
        "(assert (= (f base) #x0000))",
    ]
    for index in range(churn):
        lines.append("(declare-const e%d (_ BitVec 16))" % index)
    expected = []
    for index in range(churn):
        threshold = "#x0003" if index % 2 == 0 else "#x0027"
        lines += [
            "(push 1)",
            "(assert (bvugt (bvmul e%d e%d) %s))" %
            (index, index, threshold),
            "(check-sat)",
            "(pop 1)",
        ]
        expected.append("sat")
    lines += [
        "(push 1)",
        "(assert (= base e0))",
        "(assert (distinct (f base) (f e0)))",
        "(check-sat)",
        "(pop 1)",
        "(check-sat)",
        "(exit)",
    ]
    expected += ["unsat", "sat"]
    return "\n".join(lines) + "\n", expected


def float_congruence(size):
    """Congruence over a floating-point argument, at the sort's own equality.

    The other families are bit-vector, and the two sorts do not scale alike:
    a float actual reaches the checker through a pack/unpack boundary, and
    the query's own (= a b) is FP_SMT_EQ, which equality propagation cannot
    substitute through. Both cost more as the family grows, so the trend is
    worth its own row rather than being assumed to follow the bit-vector one.
    """
    lines = [
        "(set-logic QF_UFBVFP)",
        "(declare-fun ff ((_ FloatingPoint 8 24)) (_ BitVec 16))",
    ]
    for index in range(size):
        lines.append("(declare-const w%d (_ FloatingPoint 8 24))" % index)
    for index in range(1, size):
        lines.append("(assert (= w0 w%d))" % index)
    lines.append("(assert (distinct %s))"
                 % " ".join("(ff w%d)" % index for index in range(size)))
    lines += ["(check-sat)", "(exit)"]
    return "\n".join(lines) + "\n", ["unsat"]


def rounding_mode_exhaustion(size):
    """A rounding-mode result, ruled out mode by mode.

    Each block excludes all five modes of one application, so it is
    unsatisfiable only because the introduced result symbol is pinned to
    them. This is the shape that grows the pin rather than the congruence
    machinery.
    """
    modes = ("RNE", "RTP", "RTN", "RTZ", "RNA")
    lines = [
        "(set-logic QF_UFBVFP)",
        "(declare-fun kk ((_ BitVec 16)) RoundingMode)",
    ]
    expected = []
    for index in range(size):
        lines.append("(push 1)")
        for mode in modes:
            lines.append("(assert (distinct (kk %s) %s))" % (bv(index), mode))
        lines += ["(check-sat)", "(pop 1)"]
        expected.append("unsat")
    lines += ["(check-sat)", "(exit)"]
    expected.append("sat")
    return "\n".join(lines) + "\n", expected


FAMILIES = {
    "durable-traversal-lowering": durable_traversal,
    "define-fun-reuse": define_fun_reuse,
    "nested-let": nested_let,
    "persistent-identical-block-reuse": identical_block_reuse,
    "pop-scope": pop_scope,
    "encoding-epoch-rebuild": epoch_rebuild,
    "float-congruence": float_congruence,
    "rounding-mode-exhaustion": rounding_mode_exhaustion,
}


def invoke(stp, mode, path, timeout, epoch):
    command = [stp, "--uninterpreted-functions",
               "--incremental=" + ("on" if mode == "persistent" else "off")]
    if epoch and mode == "persistent":
        command += ["--incremental-reencode-limit=1"]
    command.append(str(path))
    started = time.monotonic()
    process = subprocess.run(command, stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT, text=True,
                             timeout=timeout, check=False)
    elapsed = time.monotonic() - started
    if process.returncode != 0:
        raise RuntimeError("benchmark command failed: %r\n%s" %
                           (command, process.stdout))
    answers = VERDICT.findall(process.stdout)
    if "unknown" in answers:
        raise RuntimeError("benchmark returned unknown: %r\n%s" %
                           (command, process.stdout))
    return answers, elapsed


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--stp", required=True)
    parser.add_argument("--scales", default="16,64")
    parser.add_argument("--repeats", type=int, default=2)
    parser.add_argument("--timeout", type=float, default=30.0)
    parser.add_argument("--evidence-out")
    args = parser.parse_args()
    scales = [int(item) for item in args.scales.split(",")]
    if not scales or any(item <= 0 for item in scales):
        parser.error("--scales must contain positive integers")
    if args.repeats <= 0:
        parser.error("--repeats must be positive")

    digest = hashlib.sha256()
    rows = []
    with tempfile.TemporaryDirectory(prefix="ufstp-perf-") as directory:
        root = Path(directory)
        for family, generator in FAMILIES.items():
            for scale in scales:
                source, expected = generator(scale)
                digest.update((family + "\0" + str(scale) + "\0").encode())
                digest.update(source.encode())
                path = root / (family + "-" + str(scale) + ".smt2")
                path.write_text(source)
                for mode in ("batch", "persistent"):
                    samples = []
                    for _ in range(args.repeats):
                        answers, elapsed = invoke(
                            args.stp, mode, path, args.timeout,
                            family == "encoding-epoch-rebuild")
                        if answers != expected:
                            raise RuntimeError(
                                "%s/%d/%s: expected %r, got %r" %
                                (family, scale, mode, expected, answers))
                        samples.append(elapsed)
                    rows.append({
                        "family": family,
                        "scale": scale,
                        "mode": mode,
                        "answer_count": len(expected),
                        "median_seconds": round(statistics.median(samples), 6),
                        "samples_seconds": [round(value, 6)
                                            for value in samples],
                    })

    evidence = {
        "schema": 1,
        "result": "pass",
        "families": list(FAMILIES),
        "scales": scales,
        "repeats": args.repeats,
        "corpus_sha256": digest.hexdigest(),
        "rows": rows,
    }
    encoded = json.dumps(evidence, indent=2, sort_keys=True) + "\n"
    if args.evidence_out:
        Path(args.evidence_out).write_text(encoded)
    print(encoded, end="")


if __name__ == "__main__":
    main()
