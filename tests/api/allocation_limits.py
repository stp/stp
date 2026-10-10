# AUTHORS: Andrew Teylu
#
# BEGIN DATE: October, 2026
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
# THE SOFTWARE.

"""An exhausted encoder reports RESOURCE through both the CLI and C++ API.

Linux RLIMIT_AS limits these children only. Sanitizers reserve a large virtual
address space before main, so CMake omits this test for instrumented builds.

A cap can also be too small for the process to start: a static binary with
its allocator linked in runs glibc's start-up allocations through that
allocator, and the first one reserves a whole segment, so a 36 MB static
mimalloc build dies inside libc under anything below about 68 MiB. That is not
a result the solver can report, so each cap is first tried on a run that does
no solving, and caps the binary cannot start under are skipped.
"""

import pathlib
import resource
import subprocess
import sys
import tempfile


QUERY = """(set-logic QF_BV)
(declare-const x (_ BitVec 512))
(declare-const y (_ BitVec 512))
(assert (= (bvmul x y) (_ bv1234567 512)))
(assert (bvugt x (_ bv1 512)))
(assert (bvugt y (_ bv1 512)))
(check-sat)
"""


def limit_address_space(mib):
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    soft, hard = resource.getrlimit(resource.RLIMIT_AS)
    limit = mib * 1024 * 1024
    if hard != resource.RLIM_INFINITY:
        limit = min(limit, hard)
    resource.setrlimit(resource.RLIMIT_AS, (limit, hard))


def starts_under(command, mib):
    """Whether the process gets as far as main and exits cleanly."""
    child = subprocess.run(command, capture_output=True, text=True, timeout=30,
                           preexec_fn=lambda: limit_address_space(mib))
    return child.returncode == 0


def main():
    cli, api = sys.argv[1:]
    backends = subprocess.check_output([api], text=True, timeout=30).split()
    assert backends, "no SAT backend available"
    with tempfile.TemporaryDirectory(prefix="stp-allocation-") as directory:
        query = pathlib.Path(directory) / "wide.smt2"
        query.write_text(QUERY)
        for backend in backends:
            for name, probe, command in (
                ("CLI", [cli, "--version"],
                 [cli, "--sat-backend", backend, str(query)]),
                ("API", [api], [api, backend, str(query)]),
            ):
                failures = 0
                # Memory requirements vary with the backend and allocator;
                # check the successful answer separately from the capped runs.
                for mib in (None, 64, 128, 256, 512):
                    if mib is not None and not starts_under(probe, mib):
                        print(f"{name} {backend} {mib} MiB: below the "
                              "start-up floor, skipped", flush=True)
                        continue
                    child = subprocess.run(
                        command, capture_output=True, text=True, timeout=30,
                        preexec_fn=(None if mib is None else
                                    lambda: limit_address_space(mib)),
                    )
                    context = (name, backend, mib, child.returncode,
                               child.stdout, child.stderr)
                    if child.returncode == 255:
                        assert "[RESOURCE]" in child.stderr, context
                        assert not child.stdout.strip(), context
                        failures += 1
                    else:
                        assert child.returncode == 0, context
                        assert child.stdout.strip() == "sat", context
                    if mib is None:
                        assert child.returncode == 0, context
                    budget = "inherited limit" if mib is None else f"{mib} MiB"
                    print(f"{name} {backend} {budget}: "
                          f"{'RESOURCE' if child.returncode == 255 else 'sat'}",
                          flush=True)
                assert failures, (name, backend, "no allocation failed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
