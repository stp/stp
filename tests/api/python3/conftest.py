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

"""Shared fixtures of the 3.x Python API tests.

Every test gets a fresh default TermManager, so symbol names never clash between
tests and the alpha's one-live-solver-per-manager rule never bites across tests.
Run with PYTHONPATH=<build>/bindings/python3 (what the CTest entry does)."""

import pytest

import stp


@pytest.fixture(autouse=True)
def fresh_manager():
    tm = stp.TermManager()
    stp.set_main_tm(tm)
    yield tm


def hard_solver(**options):
    """A solver on the default manager holding an unsat problem no backend finishes quickly:
    zext(x) * zext(y) == a 64-bit prime at 128 bits with neither factor 1 and x < y."""
    if stp.has_sat_backend("cadical"):
        options.setdefault("sat_backend", "cadical")
    options.setdefault("max_time", 120000)
    s = stp.Solver(**options)
    x, y = stp.BitVecs("hx hy", 64)
    product = stp.ZeroExt(64, x) * stp.ZeroExt(64, y)
    s.add(product == 18446744073709551557, x != 1, y != 1, stp.ULT(x, y))
    return s


@pytest.fixture
def hard():
    s = hard_solver()
    yield s
    s.close()
