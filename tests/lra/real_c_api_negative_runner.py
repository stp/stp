#!/usr/bin/env python3
"""Isolate fatal C API contracts and require their exact diagnostics."""

from __future__ import annotations

import json
import pathlib
import subprocess
import sys


CASES = {
    "null-operand": "null Expr",
    "cross-manager": "different validity checker",
    "cross-manager-equality": "different validity checker",
    "null-equality": "null Expr",
    "wrong-sort": "requires Real operands",
    "invalid-exact-text": "zero denominator",
    "value-width": "GetValueWidth",
    "index-width": "GetIndexWidth",
    "exponent-width": "GetExpWidth",
    "significand-width": "GetSigWidth",
    "real-ite-mixed-branches": "requires Real operands",
}


def main() -> int:
    if len(sys.argv) != 2:
        raise SystemExit("usage: real_c_api_negative_runner.py BINARY")
    binary = pathlib.Path(sys.argv[1]).resolve()
    results = []
    failures = []
    for mode, diagnostic in CASES.items():
        completed = subprocess.run(
            [str(binary), mode],
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )
        combined = completed.stdout + completed.stderr
        passed = completed.returncode != 0 and diagnostic in combined
        results.append(
            {
                "mode": mode,
                "return_code": completed.returncode,
                "required_diagnostic": diagnostic,
                "passed": passed,
            }
        )
        if not passed:
            failures.append(mode)
    print(json.dumps({"case_total": len(results), "failed": failures,
                      "passed": not failures}, sort_keys=True))
    return 0 if not failures else 1


if __name__ == "__main__":
    sys.exit(main())
