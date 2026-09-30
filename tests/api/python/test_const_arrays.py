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


@pytest.mark.parametrize("index_width", [1, 8])
@pytest.mark.parametrize("mode", ["auto", "on", "off"])
def test_symbolic_defaults_survive_preprocessing_and_complete_models(index_width, mode):
    v = BitVec("ca_v", 8)
    index = BitVecSort(index_width)
    a = Array("ca_symbolic", index, BitVecSort(8))
    c = K(index, v + 1)
    assert c[0].eq(v + 1)
    s = Solver(incremental=mode)
    s.add(a == c, v == 3)
    assert s.check() == sat
    m = s.model()
    assert m[a].default.as_long() == 4
    assert m.eval(a[1]).as_long() == 4
    assert m.eval(c).default.as_long() == 4
    s.push()
    s.add(a[1] != 4)
    assert s.check() == unsat
    s.pop()
    assert s.check() == sat
    assert K(_a8(), BitVecVal(1, 8) + 2).eq(K(_a8(), 3))  # a ground term is a value
    s.close()


def test_symbolic_default_equality_and_store_overwrite():
    v, w = BitVecs("ca_v ca_w", 8)
    a = Array("ca_symbolic_store", BitVecSort(8), BitVecSort(8))
    s = Solver()
    s.add(K(_a8(), v) == K(_a8(), w), v != w)
    assert s.check() == unsat
    s.close()
    s = Solver()
    s.add(a == Store(K(_a8(), v), 0, 9), v == 3)
    assert s.check() == sat
    assert s.model()[a][0].as_long() == 9
    assert s.model()[a][1].as_long() == 3
    s.add(a[1] != 3)
    assert s.check() == unsat
    s.close()


@pytest.mark.parametrize("mode", ["auto", "on", "off"])
def test_symbolic_default_can_read_another_array(mode):
    a, b = Array("ca_dst", BitVecSort(8), BitVecSort(8)), Array("ca_src", BitVecSort(8), BitVecSort(8))
    i = BitVec("ca_idx", 8)
    s = Solver(incremental=mode)
    s.add(a == K(_a8(), b[i] + 1), b[i] == 6)
    assert s.check() == sat
    assert s.model()[a].default.as_long() == 7
    s.push()
    s.add(a[2] != 7)
    assert s.check() == unsat
    s.pop()
    assert s.check() == sat
    assert s.model()[a].default.as_long() == 7
    s.close()


@pytest.mark.parametrize("mode", ["auto", "on", "off"])
def test_symbolic_default_cannot_define_an_array_through_itself(mode):
    a = Array("ca_self", BitVecSort(8), BitVecSort(8))
    i = BitVec("ca_self_i", 8)
    s = Solver(incremental=mode)
    s.add(a == K(_a8(), a[i] + 1))
    assert s.check() == unsat
    s.close()


@pytest.mark.parametrize("mode", ["auto", "on", "off"])
def test_symbolic_defaults_with_mutual_array_dependencies(mode):
    a = Array("ca_cycle_a", BitVecSort(8), BitVecSort(8))
    b = Array("ca_cycle_b", BitVecSort(8), BitVecSort(8))
    i, j = BitVecs("ca_cycle_i ca_cycle_j", 8)
    s = Solver(incremental=mode)
    s.add(a == K(_a8(), b[i] + 1), b == K(_a8(), a[j] - 1))
    assert s.check() == sat
    m = s.model()
    assert bool(m.eval(a == K(_a8(), b[i] + 1))) is True
    assert bool(m.eval(b == K(_a8(), a[j] - 1))) is True
    s.push()
    s.add(b == K(_a8(), a[j]))
    assert s.check() == unsat
    s.pop()
    assert s.check() == sat
    s.close()


def test_symbolic_default_parses_and_round_trips():
    s = Solver()
    s.from_string("(declare-fun ca_z () (_ BitVec 8)) (assert (= ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x00) "
                  "(store ((as const (Array (_ BitVec 8) (_ BitVec 8))) ca_z) #x00 #x00)))")
    assert s.check() == sat
    assert s.model().eval(BitVec("ca_z", 8)).as_long() == 0
    script = s.to_smt2(with_check_sat=True)
    other = Solver(tm=TermManager())
    other.from_string(script)
    assert other.check() == sat
    other.close()
    s.close()


def test_symbolic_float_default_is_lowered_before_checker_preparation():
    x = FP("ca_float_x", Float32())
    a = Array("ca_float_a", BitVecSort(8), Float32())
    value = fpAdd(RNE(), x, FPVal(1.25, Float32()))
    s = Solver()
    s.add(a == K(BitVecSort(8), value), x == FPVal(2.5, Float32()))
    assert s.check() == sat
    assert float(s.model()[a].default) == 3.75
    s.add(Not(fpEQ(a[2], FPVal(3.75, Float32()))))
    assert s.check() == unsat
    s.close()


@pytest.mark.parametrize("mode", ["auto", "on", "off"])
def test_float_conversion_hidden_in_a_bitvector_default(mode):
    x = FP("ca_hidden_float", Float32())
    a = Array("ca_hidden_conversion", BitVecSort(8), BitVecSort(8))
    s = Solver(incremental=mode)
    # The conversion is the only FP operation in the first check's assertions.
    s.add(a == K(_a8(), fpToUBV(RNE(), x, 8)))
    assert s.check() == sat
    s.push()
    s.add(x == FPVal(2.5, Float32()))
    assert s.check() == sat
    assert s.model()[a].default.as_long() == 2
    assert s.model().eval(a[9]).as_long() == 2
    s.add(a[9] != 2)
    assert s.check() == unsat
    s.pop()
    assert s.check() == sat
    s.close()


@pytest.mark.parametrize("mode", ["auto", "on", "off"])
def test_nested_symbolic_float_defaults_are_prepared_iteratively(mode):
    x, y = FP("ca_nested_x", Float32()), FP("ca_nested_y", Float32())
    i, j = BitVecs("ca_nested_i ca_nested_j", 8)
    a = Array("ca_nested", BitVecSort(8), Float32())
    c = K(BitVecSort(8), x)
    for _ in range(19):
        c = K(BitVecSort(8), Store(c, i, y)[j])
    s = Solver(incremental=mode)
    s.add(a == c)
    assert s.check() == sat
    s.push()
    s.add(i == j, y == FPVal(3.0, Float32()))
    assert s.check() == sat
    assert float(s.model()[a].default) == 3.0
    s.add(Not(fpEQ(a[9], FPVal(3.0, Float32()))))
    assert s.check() == unsat
    s.pop()
    assert s.check() == sat
    s.close()


def test_default_refuses_theories_that_need_earlier_preparation():
    x = BitVec("ca_uf_x", 8)
    f = Function("ca_uf", BitVecSort(8), BitVecSort(8))
    with pytest.raises(Unsupported):
        K(BitVecSort(8), f(x))
    a = Array("ca_condition_a", BitVecSort(8), BitVecSort(8))
    b = Array("ca_condition_b", BitVecSort(8), BitVecSort(8))
    with pytest.raises(Unsupported):
        K(BitVecSort(8), If(a == b, x, x + 1))


def test_symbolic_rounding_mode_in_a_float_default_is_pinned():
    mode = Const("ca_mode", RoundingModeSort())
    value = fpRoundToIntegral(mode, FPVal(1.5, Float32()))
    a = Array("ca_round_a", BitVecSort(8), Float32())
    s = Solver()
    s.add(a == K(BitVecSort(8), value))
    assert s.check() == sat
    assert s.model().eval(mode).sexpr() in {"RNE", "RNA", "RTP", "RTN", "RTZ"}
    assert float(s.model()[a].default) in {1.0, 2.0}
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
