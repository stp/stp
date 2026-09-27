#********************************************************************
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
#********************************************************************

"""Constant arrays: equality, distinct, store chains and if-then-else over them are
decided, the model completes an equated array with the default, and the as-const
spelling round-trips through the parser."""

import pytest

from stp import *

SPELLED = "((as const (Array (_ BitVec 8) (_ BitVec 8))) #x07)"


def _a8():
    """The array sort on the test's own manager (the fixture replaces it per test)."""
    return ArraySort(BitVecSort(8), BitVecSort(8))


def test_equality_and_model_completion():
    a = Array("ca_a", BitVecSort(8), BitVecSort(8))
    c7 = K(_a8(), 7)
    s = Solver()
    s.add(a == c7)
    assert s.check() == sat
    m = s.model()
    assert bool(m.eval(a == c7)) is True
    assert bool(m.eval(a != c7)) is False
    assert m.eval(a[200]).as_long() == 7
    assert m.eval(a[0]).as_long() == 7
    v = m[a]
    assert v.default.as_long() == 7
    assert v[200].as_long() == 7
    assert SPELLED in m.sexpr()
    assert "constarray" not in m.sexpr()
    i = BitVec("ca_i", 8)
    s.add(a[i] != 7)
    assert s.check() == unsat
    s.close()


def test_disequality_witness_store_chain_and_two_constants():
    a = Array("ca_b", BitVecSort(8), BitVecSort(8))
    c7 = K(_a8(), 7)
    s = Solver()
    s.add(a != c7)
    assert s.check() == sat
    m = s.model()
    v = m[a]
    assert v.default.as_long() != 7 or any(el.as_long() != 7 for _, el in v.items())
    s.close()

    chain = Store(c7, 5, 42)
    s = Solver()
    s.add(a == chain)
    assert s.check() == sat
    m = s.model()
    assert m.eval(a[5]).as_long() == 42 and m.eval(a[9]).as_long() == 7
    assert m[a].default.as_long() == 7 and m[a][5].as_long() == 42
    assert bool(m.eval(a == chain)) is True
    s.close()

    s = Solver()
    s.add(a == K(_a8(), 1), a == K(_a8(), 2))
    assert s.check() == unsat
    s.close()


def test_constant_arrays_against_each_other():
    c1, c2 = K(_a8(), 1), K(_a8(), 2)
    assert K(_a8(), 1).eq(c1)
    assert bool(c1 == K(_a8(), 1)) is True  # the same array, folded
    assert bool(c1 == c2) is False
    s = Solver()
    s.add(Distinct(c1, c2))
    assert s.check() == sat
    s.close()
    v, w = BitVecs("ca_v ca_w", 8)
    s = Solver()
    s.add(K(_a8(), v) == K(_a8(), w), v != w)
    assert s.check() == unsat
    s.close()


def test_array_ite_with_a_constant_branch():
    a = Array("ca_c", BitVecSort(8), BitVecSort(8))
    d = Array("ca_d", BitVecSort(8), BitVecSort(8))
    b = Bool("ca_p")
    sel = If(b, K(_a8(), 1), d)
    s = Solver()
    s.add(a == sel, b, a[2] != 1)
    assert s.check() == unsat
    s.close()
    s = Solver()
    s.add(a == sel, b, a[2] == 1)
    assert s.check() == sat
    assert s.model()[a].default.as_long() == 1
    s.close()


def test_other_element_sorts():
    f = Array("ca_f", BitVecSort(4), Float32())
    cf = K(ArraySort(BitVecSort(4), Float32()), 1.5)
    i = BitVec("ca_i4", 4)
    s = Solver()
    s.add(f == cf, Not(fpEQ(f[i], 1.5)))
    assert s.check() == unsat
    s.close()
    r = Array("ca_r", BitVecSort(4), RoundingModeSort())
    cr = K(ArraySort(BitVecSort(4), RoundingModeSort()), RTZ())
    s = Solver()
    s.add(r == cr, r[i] != RTZ())
    assert s.check() == unsat
    s.close()


def test_spelling_and_parsing_round_trip():
    c7 = K(_a8(), 7)
    assert c7.sexpr() == SPELLED
    assert c7.kind() == Kind.CONST_ARRAY
    s = Solver()
    assert s.parse_term(SPELLED).eq(c7) if hasattr(s, "parse_term") else True
    fs = parse_smt2_string("(declare-fun ca_z () (Array (_ BitVec 8) (_ BitVec 8))) (assert (= ca_z " + SPELLED + "))")
    s.add(*fs)
    assert s.check() == sat
    z = Array("ca_z", BitVecSort(8), BitVecSort(8))
    assert s.model().eval(z[100]).as_long() == 7
    s.close()
    with pytest.raises(ParseError):
        parse_smt2_string("(assert (= (select ((as const (Array (_ BitVec 8) (_ BitVec 8))) #b1) #x00) #x00))")


def test_reads_fold_at_construction():
    c7 = K(_a8(), 7)
    i = BitVec("ca_j", 8)
    assert c7[i].kind() == Kind.VALUE and c7[i].as_long() == 7
