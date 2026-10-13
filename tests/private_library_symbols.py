#!/usr/bin/env python3
"""Check that libstp's version map preserves its private dependency boundary."""

import re
import subprocess
import sys

nm, library = sys.argv[1:]
output = subprocess.check_output(
    [nm, "--dynamic", "--defined-only", "--format=posix", library], text=True
)
symbols = {line.split()[0] for line in output.splitlines() if line.strip()}
if not symbols:
    raise SystemExit("FAIL: no defined dynamic symbols found in " + library)
missing = {"stp_get_version", "stp_solver_check_sat"} - symbols
if missing:
    raise SystemExit("FAIL: public API symbols missing: " + ", ".join(sorted(missing)))

# The map hides weak template instantiations involving private LRA types.
# --exclude-libs hides the ABC archive; a global wildcard in the
# map used to override that under LLD and retain otherwise unused ABC code.
private = re.compile(r"^(?:Abc_|Gia_|Cnf_|_Z.*3stp3lra)")
leaked = sorted(name for name in symbols if private.match(name))
if leaked:
    raise SystemExit("FAIL: private symbols exported:\n" + "\n".join(leaked))
print("PASS: private LRA and ABC symbols remain hidden")
