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

"""Seven small end-to-end programs, one per theory and one for solver control, with
their expected outcomes; the C++ versions are in tests/api/cpp/rosetta.cpp.
R4's `b == c` is an equality against a store over a constant array."""

from fractions import Fraction

import pytest

from stp import *


def test_r1_bitvectors(capsys):
    x, y = BitVecs('x y', 32); w = BitVec('w', 128)
    s = Solver()
    s.add(x * 3 == 7, y == LShR(x, 1), w == ZeroExt(96, x) << 64)
    assert s.check() == sat
    m = s.model()
    print(m[x].as_long(), m[x].as_signed_long(), m[x].as_hex_string(), m[y].as_long(), m[w].as_long())
    out = capsys.readouterr().out.split()
    assert m[x].as_long() == 0xAAAAAAAD and out[0] == "2863311533" and out[1] == "-1431655763" and out[2] == "aaaaaaad"
    assert m[y].as_long() == 0xAAAAAAAD >> 1 and m[w].as_long() == 0xAAAAAAAD << 64
    with pytest.raises(TypeError):
        assert s.check()  # a result has no truth value
    s.close()


def test_r2_floating_point(capsys):
    a, b, rm = FP('a', Float32()), FP('b', Float64()), Const('rm', RoundingModeSort())
    s = Solver()
    s.add(fpEQ(fpAdd(RNE(), a, 1.5), 3.0), Not(fpIsNaN(b)), b < 0.0)
    one3 = lambda mode: fpDiv(mode, FPVal(1.0, Float64()), 3.0)  # noqa: E731
    s.add(Not(fpEQ(one3(rm), one3(RNE()))))
    assert s.check() == sat
    m = s.model(); av, bv = m[a], m[b]
    print(float(av), hex(av.bits()), (av.sign(), av.exponent(), av.significand()))
    cls = 'nan' if bv.isNaN() else 'inf' if bv.isInf() else 'zero' if bv.isZero() else 'subnormal' if bv.isSubnormal() else 'normal'
    print(float(bv), cls)
    print(m[rm].as_rounding_mode().name)
    out = capsys.readouterr().out.splitlines()
    assert abs(float(av) + 1.5 - 3.0) <= 2 ** -22 and float(bv) < 0 and cls in ('normal', 'subnormal', 'inf')
    assert m[rm].as_rounding_mode() != RoundingMode.RNE and out[2] in ("RNA", "RTP", "RTN", "RTZ")
    assert av.sign() is False and 0 <= av.significand() < 2 ** 23
    s.close()


def test_r3_reals():
    x, y = Reals('x y'); s = Solver()
    s.add(3 * x + 2 * y == 1, x > Q(1, 2))
    assert s.check() == sat
    m = s.model()
    xv, yv = m[x].as_fraction(), m[y].as_fraction()
    assert isinstance(xv, Fraction) and 3 * xv + 2 * yv == 1 and xv > Fraction(1, 2)
    assert float(m[x]) == float(xv) and float(m[y]) == float(yv)
    with pytest.raises(Unsupported):
        x * y
    with pytest.raises(TypeError):
        0.5 * x
    s.close()


def test_r4_arrays():
    A = ArraySort(BitVecSort(32), BitVecSort(8))
    a, b = Array('a', BitVecSort(32), BitVecSort(8)), Array('b', BitVecSort(32), BitVecSort(8))
    c = Store(K(A, 0), 5, 0x2a)
    s = Solver(); s.add(a != b, a[0] == b[0])
    s.add(b == c)  # an equality against a store over a constant array
    assert s.check() == sat
    m = s.model()
    assert is_true(m.eval(b == c)) and m[b].default.as_long() == 0
    for arr in (a, b):
        items, default = m[arr].items(), m[arr].default
        assert all(isinstance(k, BitVecNumRef) and isinstance(v, BitVecNumRef) for k, v in items)
        assert isinstance(default, BitVecNumRef)
    assert m[b][5].as_long() == 0x2a and m[b][0].as_long() == 0 and m[b][1].as_long() == 0
    assert m[a][0].as_long() == m[b][0].as_long()
    assert isinstance(m.eval(a[5]), BitVecNumRef) and m.eval(a[5]).as_long() == m[a][5].as_long()
    # a and b differ somewhere
    assert any(m[a][k.as_long()].as_long() != m[b][k.as_long()].as_long() for k, _ in m[a].items() + m[b].items()) \
        or m[a].default.as_long() != m[b].default.as_long()
    assert K(A, BitVecVal(0, 8)) is K(A, 0)
    s.close()


def test_r5_uninterpreted_functions(capsys):
    B8 = BitVecSort(8)
    f, g = Function('f', B8, B8), Function('g', B8, B8, BoolSort())
    x, y = BitVecs('x y', 8)
    s = Solver(); s.add(f(x) != f(y), g(x, f(x)), x == 3)
    assert s.check() == sat
    m = s.model()
    for fn in (f, g):
        print(fn, list(m[fn]), m[fn].else_value())
    print(m.eval(f(3)), m.eval(f(y)))
    out = capsys.readouterr().out.splitlines()
    assert out[0].startswith("f ") and out[1].startswith("g ") and len(out) == 3
    f3, fy = m.eval(f(3)), m.eval(f(y))
    assert isinstance(f3, BitVecNumRef) and isinstance(fy, BitVecNumRef) and f3.as_long() != fy.as_long()
    assert m[f](3).as_long() == f3.as_long() and bool(m[g](3, f3.as_long())) is True
    assert len(m[f]) >= 1 and m[f].arity() == 1 and m[g].arity() == 2
    with pytest.raises(ArgumentError):
        f(1, 2)
    s.close()


def test_r6_solver_control(capsys):
    s = Solver(max_time=500, random_seed=7)
    with s:
        p, x = Bool('p'), BitVec('x', 32)
        s.add(Implies(p, x == 0))
        r = s.check(p, x != 0)
        if r == unsat: print('failed:', s.unsat_assumptions())
    r = s.check()
    if r == unknown: print('unknown:', r.reason.name, r.reason_message)
    else: print(r)
    out = capsys.readouterr().out.splitlines()
    assert out[0].startswith("failed: [") and "p" in out[0] and out[1] == "sat"
    assert s.options["max_time"] == 500 and s.options["timeout"] == 500 and s.options["random_seed"] == 7
    with pytest.raises(TypeError):
        if r:
            pass
    s.close()


def test_r7_errors(capsys):
    u, v = BitVec('u', 8), BitVec('v', 16)
    try: u + v
    except SortMismatch as e: print(e.code.name, e.argument_index, e)
    s = Solver(); s.add(u == 1)
    print('solver still works:', s.check())
    out = capsys.readouterr().out.splitlines()
    assert out[0].startswith("SORT_MISMATCH 1 ") and "(_ BitVec 16)" in out[0] and "(_ BitVec 8)" in out[0]
    assert out[1] == "solver still works: sat"
    with pytest.raises(TypeError):  # also catchable as TypeError
        u + v
    s.close()
