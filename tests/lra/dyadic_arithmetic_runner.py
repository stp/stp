#!/usr/bin/env python3
"""Independent Fraction oracle around word, double-word and big-number edges."""
from fractions import Fraction
from pathlib import Path
import random
import subprocess
import sys
import tempfile


def main():
    rng = random.Random(620126)
    edges = (0, 1, 2, 30, 31, 32, 60, 61, 62, 63, 64, 65, 100,
             123, 124, 125, 126, 127, 128, 129, 255)
    corpus = []
    expected = []
    operations = ("add", "sub", "mul", "div", "cmp", "canonical")
    for i in range(20006):  # the arithmetic driver's corpus mode pins this size
        fractions = []
        for side in range(2):
            bits = edges[(i + 7 * side) % len(edges)]
            shift = edges[rng.randrange(len(edges))]
            odd = rng.getrandbits(bits) | 1
            numerator = odd << rng.randrange(0, 4)
            if rng.randrange(2):
                numerator = -numerator
            if i % 137 == 0:
                numerator = 0
            # Mix powers of two with shared odd factors, so the general
            # binary-GCD path is exercised alongside the dyadic shortcut.
            denominator = (1 << shift) * (rng.choice((1, 1, 3, 7, 15)))
            fractions.append((f"{numerator}/{denominator}", Fraction(numerator, denominator)))
        (left, a), (right, b) = fractions
        op = operations[i % len(operations)]
        corpus.append(f"{op}\t{left}\t{right}\n")
        if op == "add":
            value = a + b
        elif op == "sub":
            value = a - b
        elif op == "mul":
            value = a * b
        elif op == "div":
            value = a / b if b else "ERROR"
        elif op == "cmp":
            value = (a > b) - (a < b)
        else:
            value = a
        expected.append(f"{i}\t{value}")
    with tempfile.TemporaryDirectory(prefix="stp-dyadic-") as directory:
        root = Path(directory)
        (root / "input.tsv").write_text("".join(corpus))
        run = subprocess.run([sys.argv[1], "corpus", str(root / "input.tsv"),
                              str(root / "output.tsv")], capture_output=True,
                             text=True, timeout=60)
        assert run.returncode == 0, run.stdout + run.stderr
        actual = (root / "output.tsv").read_text().splitlines()
        assert len(actual) == len(expected), (len(actual), len(expected))
        for i, (got, want) in enumerate(zip(actual, expected)):
            assert got == want, (corpus[i], got, want)
    print("20,006 exact arithmetic results agree with Python Fraction")


if __name__ == "__main__":
    main()
