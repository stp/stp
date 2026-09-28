# AUTHORS: Andrew Teylu
#
# BEGIN DATE: September, 2026
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

"""Allocator behaviour of the stp Python package.

The stp executables link a fast allocator statically, which interposes malloc
for the whole process. The Python package is different: its extension loads
libstp into an interpreter that has already been allocating with the C
library, so the allocator has to be chosen for the process rather than baked
into the library. These tests pin both halves of that contract:

  * libstp must not embed an allocator of its own. If it did, memory could be
    allocated by libstp's allocator and freed by the interpreter's (or the
    reverse) and the mixed heaps would eventually corrupt.
  * When an allocator *is* preloaded into the interpreter, libstp's
    allocations must actually go through it, and results must be unchanged.

A unittest script, run by ctest as python3-allocator-tests with libstp's path,
the preloadable allocator's path (empty when none was built) and the
allocator's name as its arguments, and the package on PYTHONPATH."""

import os
import re
import subprocess
import sys
import unittest

LIBSTP, PRELOADABLE_ALLOCATOR, ALLOCATOR_NAME = sys.argv[1:4]
del sys.argv[1:4]

ALLOCATOR_SYMBOLS = {
    "malloc", "free", "realloc", "calloc",
    "_Znwm", "_Znam", "_ZdlPv", "_ZdaPv",
}

SOLVE_SNIPPET = """
from stp import BitVecs, Solver, sat
a, b = BitVecs("a b", 8)
s = Solver()
s.add(a + b == 10, a == 3)
assert s.check() == sat, "expected sat"
print("RESULT", s.model()[b].as_long())
"""


def _solve_in_child(env):
    return subprocess.run(
        [sys.executable, "-c", SOLVE_SNIPPET],
        stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        env=dict(os.environ, **env), universal_newlines=True,
    )


class TestPythonAllocator(unittest.TestCase):
    def test_the_package_solves_correctly(self):
        """The package works in-process under the configured build."""
        from stp import BitVecs, Solver, sat
        a, b = BitVecs("a b", 8)
        s = Solver()
        s.add(a + b == 10, a == 3)
        self.assertEqual(s.check(), sat)
        self.assertEqual(s.model()[b].as_long(), 7)

    def test_libstp_does_not_embed_an_allocator(self):
        """libstp must leave the allocator to the process that loads it.

        The allocator is linked into the stp executables, never into the
        library. Linking it here instead would give a Python user two heaps in
        one process.
        """
        if not sys.platform.startswith("linux"):
            self.skipTest("symbol inspection is Linux-specific")
        try:
            out = subprocess.check_output(
                ["nm", "-D", "--defined-only", LIBSTP], universal_newlines=True)
        except (OSError, subprocess.CalledProcessError):
            self.skipTest("nm unavailable")

        defined = set()
        for line in out.splitlines():
            parts = line.split()
            # "<addr> <type> <name>", or "<type> <name>" for undefined-address
            if len(parts) >= 2 and parts[-2] in ("T", "W", "i"):
                defined.add(parts[-1])

        clash = defined & ALLOCATOR_SYMBOLS
        self.assertEqual(
            clash, set(),
            "libstp defines allocator symbols %s. The allocator belongs on the "
            "executables (STP_ALLOCATOR_LIBRARY), not on the library: a Python "
            "process would end up allocating with one heap and freeing with "
            "another." % sorted(clash))

    def test_preloaded_allocator_serves_libstp(self):
        """With an allocator preloaded, libstp's allocations go through it.

        This is what a Python user does to get the same allocator the stp
        binary uses: LD_PRELOAD it into the interpreter.
        """
        if not sys.platform.startswith("linux"):
            self.skipTest("LD_PRELOAD is Linux-specific")
        if not PRELOADABLE_ALLOCATOR or not os.path.exists(PRELOADABLE_ALLOCATOR):
            self.skipTest("no preloadable allocator was built (STP_ALLOCATOR=%s)"
                          % ALLOCATOR_NAME)

        # Correct answer under the preloaded allocator.
        child = _solve_in_child({"LD_PRELOAD": PRELOADABLE_ALLOCATOR})
        self.assertEqual(child.returncode, 0,
                         "solve failed under LD_PRELOAD:\n%s" % child.stderr)
        self.assertIn("RESULT 7", child.stdout)

        # ...and it really was that allocator serving libstp, not the C library.
        child = _solve_in_child({"LD_PRELOAD": PRELOADABLE_ALLOCATOR,
                                 "LD_DEBUG": "bindings"})
        if "symbol=" not in child.stderr and "binding file" not in child.stderr:
            self.skipTest("loader diagnostics unavailable")

        allocator = os.path.basename(PRELOADABLE_ALLOCATOR)
        pattern = re.compile(
            r"binding file \S*libstp\S* \[0\] to \S*" + re.escape(allocator)
            + r"\S* \[0\]: normal symbol `(?:malloc|free|_Znwm)'")
        self.assertTrue(
            pattern.search(child.stderr),
            "libstp did not bind malloc to the preloaded %s; something in the "
            "build is defeating symbol interposition" % allocator)


if __name__ == '__main__':
    suite = unittest.TestLoader().loadTestsFromTestCase(TestPythonAllocator)
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    sys.exit(0 if result.wasSuccessful() else 1)
