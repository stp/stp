#!/usr/bin/env python3
"""Isolate the private-atom public-printer fail-closed contract."""

from __future__ import annotations

import json
import pathlib
import subprocess
import sys


def main() -> int:
    if len(sys.argv) != 2:
        raise SystemExit("usage: real_frontend_negative_runner.py BINARY")
    binary = pathlib.Path(sys.argv[1]).resolve()
    completed = subprocess.run(
        [str(binary), "internal-print-barrier"],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    diagnostic = "refuses to expose an implementation-generated symbol"
    passed = completed.returncode != 0 and diagnostic in (
        completed.stdout + completed.stderr
    )
    print(json.dumps({"return_code": completed.returncode,
                      "required_diagnostic": diagnostic,
                      "passed": passed}, sort_keys=True))
    return 0 if passed else 1


if __name__ == "__main__":
    sys.exit(main())
