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

"""Models: values of every sort, arrays and functions as data, completion versus lookup,
evaluation, printing, pickling and translation."""

import pickle
from fractions import Fraction

import pytest

from stp import *
import stp


def _model(*fs):
    s = Solver()
    s.add(*fs)
    assert s.check() == sat
    m = s.model()
    s.close()
    return m


def test_scalar_values():
    p = Bool("p")
    x = BitVec("x", 8)
    w = BitVec("w", 128)
    a = FP("a", Float32())
    rm = Const("rm", RoundingModeSort())
    r = Real("r")
    m = _model(p, x == 200, w == (1 << 100) + 7, fpEQ(a, 2.5), rm == RTZ(), r == Q(-3, 7))
    assert isinstance(m[p], BoolNumRef) and bool(m[p]) is True and m[p].kind() == Kind.VALUE
    v = m[x]
    assert isinstance(v, BitVecNumRef) and v.as_long() == 200 and v.as_signed_long() == -56 and int(v) == 200
    assert v.as_binary_string() == "11001000" and v.as_hex_string() == "c8" and v.as_bytes() == b"\xc8"
    assert m[w].as_long() == (1 << 100) + 7 and len(m[w].as_bytes()) == 16
    fv = m[a]
    assert isinstance(fv, FPNumRef) and float(fv) == 2.5 and fv.as_fraction() == Fraction(5, 2)
    assert fv.sign() is False and fv.exponent() == 128 and fv.exponent(biased=False) == 1 and fv.significand() == 1 << 21
    assert fv.bits() == 0x40200000 and fv.isNormal()
    assert isinstance(m[rm], RMNumRef) and m[rm].as_rounding_mode() == RoundingMode.RTZ
    rv = m[r]
    assert isinstance(rv, RatNumRef) and rv.as_fraction() == Fraction(-3, 7) and float(rv) == -3 / 7
    assert rv.numerator() == -3 and rv.denominator() == 7 and rv.as_string() == "-3/7"
    assert m.eval(x + 1).as_long() == 201 and m.eval(x + 1) is m[x + 1]
    assert m.eval(True) is BoolVal(True) and m.eval(p & True) is BoolVal(True)
    assert m.values([x, w])[0].as_long() == 200 and len(m.values([x, w])) == 2
    assert set(d.decl_name() for d in m.decls()) == {"p", "x", "w", "a", "rm", "r"}
    assert len(m) == 6 and set(m) == set(m.decls())
    assert m.in_core(x) and not m.in_core(BitVec("zz", 8))
    assert m.manager() is main_tm()
    with pytest.raises(TypeError):
        m[3]


def test_completion_versus_lookup():
    x, y = BitVecs("x y", 8)
    m = _model(x == 5)
    assert m[x].as_long() == 5 and m.get(x).as_long() == 5
    with pytest.raises(KeyError) as e:
        m[y]
    assert "y" in str(e.value)
    with pytest.raises(KeyError):
        m[x + y]
    assert m.get(y) is None and m.get(y, 7) == 7 and y not in m and x in m
    assert m.eval(y).as_long() == 0  # completion: the sort's default
    assert m.eval(x + y).as_long() == 5 and m.evaluate(x + y).as_long() == 5
    assert isinstance(m.eval(y), BitVecNumRef)
    # model_completion=False substitutes the core and leaves the rest in place
    t = m.eval(x + y, model_completion=False)
    assert not t.is_value() and t.kind() == Kind.BV_ADD and any(c is y for c in t.children())
    assert m.eval(x + 1, model_completion=False).as_long() == 6
    assert m.eval(y, model_completion=False) is y
    # every sort's default
    a = FP("a", Float32())
    r = Real("r")
    p = Bool("p")
    rm = Const("rm", RoundingModeSort())
    arr = Array("arr", BitVecSort(32), BitVecSort(8))
    assert m.eval(a).isZero() and not m.eval(a).isNegative()
    assert m.eval(r).as_fraction() == 0 and bool(m.eval(p)) is False
    assert m.eval(rm).as_rounding_mode() == RoundingMode.RNE
    assert m.eval(arr)[3].as_long() == 0 and m.eval(arr).default.as_long() == 0


@pytest.mark.parametrize("reencode_limit", [0, 1])
def test_incremental_lazy_read_completion_after_rebuild(reencode_limit):
    # A partial-width read still needs every bit of its refinement symbols.
    # Repeated scopes exercise reuse and promotion; a low relief threshold
    # also forces reconstruction as popped encodings accumulate.
    a = Array("completion_array", BitVecSort(8), BitVecSort(32))
    indices = BitVecs("completion_i completion_j completion_k", 8)
    values = BitVecs("completion_v completion_w completion_z", 32)
    query = BitVec("completion_query", 8)
    chain = a
    for index, value in zip(indices, values):
        chain = Store(chain, index, value)
    cell = Select(chain, query)
    solver = Solver(incremental="on", incremental_reencode_limit=reencode_limit,
                    incremental_base_resimplify_limit=0, check_sanity=True)
    solver.add(Extract(0, 0, cell) == 1)
    try:
        for round in range(48):
            solver.push()
            # Use a new circuit each round so relief cannot just reuse roots.
            extra = BitVec(f"completion_extra_{round}", 8)
            solver.add(UGT(extra * extra, 3))
            solver.add(cell == 0xDEADBEEF)
            assert solver.check() == sat
            assert solver.model().eval(cell).as_long() == 0xDEADBEEF
            solver.pop()
        # Returning to the original partial read, then binding its upper bits
        # differently, must work after both backend and complete epoch resets.
        assert solver.check() == sat
        solver.push()
        solver.add(cell == 0x12345679)
        assert solver.check() == sat
        assert solver.model().eval(cell).as_long() == 0x12345679
        solver.add(Extract(0, 0, cell) == 0)
        assert solver.check() == unsat
        solver.pop()
        assert solver.check() == sat
    finally:
        solver.close()


@pytest.mark.parametrize("simplify", [False, True])
@pytest.mark.parametrize("fill", ["zero", "ones"])
def test_array_equality_without_completion(simplify, fill):
    tm = TermManager(simplify=simplify)
    bv = tm.bv_sort(2)
    arrays = tm.array_sort(bv, bv)
    a, b, c = [tm.declare(name, arrays) for name in ("a", "b", "c")]
    k = tm.mk_const_array(arrays, tm.mk_bv(2, 0))
    s = Solver(tm)
    s.set("model-array-fill", fill)
    assert s.check() == sat
    m = s.model()
    assert not m.in_core(a) and not m.in_core(b)
    assert m.try_value(a) is None and m.try_value(b) is None
    # Completing reads still answer, but do not change subsequent lookups.
    assert bool(m.eval(a == b)) is True
    assert bool(m.eval(a != b)) is False
    assert bool(m.eval(a == k)) is (fill == "zero")
    for t in (a == b, a != b, a == k, k == b, Distinct(a, b, c),
              Store(a, 0, 1) == Store(b, 0, 1)):
        assert m.try_value(t) is None
        with pytest.raises(KeyError):
            m[t]
        assert m.get(t) is None
        assert not m.eval(t, model_completion=False).is_value()
    assert bool(m[a == a]) is True
    assert bool(m[a != a]) is False
    # All four indices are overwritten, so neither absent base is needed.
    full_a, full_b = a, b
    for i in range(4):
        full_a, full_b = Store(full_a, i, i), Store(full_b, i, i)
    assert bool(m[full_a == full_b]) is True
    assert bool(m[full_a != full_b]) is False
    assert not m.in_core(a) and not m.in_core(b)


def test_array_and_function_terms_in_the_value_readers():
    a = Array("a", BitVecSort(32), BitVecSort(8))
    b = Array("b", BitVecSort(32), BitVecSort(8))
    i, j = BitVecs("i j", 32)
    f = Function("f", BitVecSort(8), BitVecSort(8))
    x = BitVec("x", 8)
    m = _model(a[5] == 42, a[i] == 7, i == 100, f(x) == 3)
    # an array's value is a term with no symbol in it
    va = m.values([a])[0]
    assert isinstance(va, ArrayRef) and not va.is_const() and va.id == m[a].id
    assert m.eval(va[5]).as_long() == 42 and m.eval(va[100]).as_long() == 7
    # the mapping rule: a store at a symbol of the core is a value, one at a symbol outside it is not
    assert m[Store(a, i, 9)][100].as_long() == 9 and m[Store(a, i, 9)][5].as_long() == 42
    with pytest.raises(KeyError) as e:
        m[Store(a, j, 9)]
    assert "j" in str(e.value)
    with pytest.raises(KeyError):
        m[b]
    # a function has no value term
    with pytest.raises(SortMismatch):
        m.values([f])
    assert m[f] is not None and m.eval(f) is not None


def test_array_values():
    A = ArraySort(BitVecSort(32), BitVecSort(8))
    a = Array("a", BitVecSort(32), BitVecSort(8))
    i = BitVec("i", 32)
    m = _model(a[5] == 42, a[6] == 43, a[i] == 7, i == 100)
    v = m[a]
    assert isinstance(v, ArrayNumRef) and isinstance(v, ArrayRef) and v.sort() is A
    assert v.default.as_long() == 0 and isinstance(v.default, BitVecNumRef)
    items = v.items()
    assert [(k.as_long(), e.as_long()) for k, e in items] == sorted((k.as_long(), e.as_long()) for k, e in items)
    d = {k.as_long(): e.as_long() for k, e in items}
    assert d[5] == 42 and d[6] == 43 and d[100] == 7 and len(v) == len(items) and len(v) >= 3
    assert [k.as_long() for k in v.keys()] == [k.as_long() for k, _ in items] and list(v) == v.keys()
    assert v[5].as_long() == 42 and v[BitVecVal(6, 32)].as_long() == 43 and v[7].as_long() == 0
    assert 5 in v and 7 not in v and BitVecVal(100, 32) in v
    assert v[i].kind() in (Kind.SELECT, Kind.ITE)  # a symbolic index selects (the engine expands a select over a constant array)
    assert v.as_bytes(4, 4) == b"\x00\x2a\x2b\x00" and m.array_bytes(a, 4, 4) == b"\x00\x2a\x2b\x00"
    assert v.as_bytes(99, 2) == b"\x00\x07" and v.as_bytes(100, 1) == b"\x07"
    assert v.as_term() is v and v.kind() in (Kind.STORE, Kind.CONST_ARRAY)
    assert m.eval(a[5]).as_long() == 42 and m[a[5]].as_long() == 42 and m.eval(a)[5].as_long() == 42
    assert Default(v).as_long() == 0
    # a fresh array symbol: completion gives the constant array of the element default
    b = Array("b", BitVecSort(32), BitVecSort(8))
    with pytest.raises(KeyError):
        m[b]
    assert m.eval(b).default.as_long() == 0 and len(m.eval(b)) == 0 and m.eval(b)[1].as_long() == 0
    wide = Array("wide", BitVecSort(8), BitVecSort(12))
    m2 = _model(wide[1] == 5)
    with pytest.raises(ArgumentError):
        m2[wide].as_bytes(0, 2)  # element width not a multiple of 8
    with pytest.raises(ArgumentError):
        m2.array_bytes(wide, 0, 2)
    # a term that is no array is refused without leaving the refusal behind
    # for the next, unrelated call to report
    x = BitVec("x_bytes", 8)
    m3 = _model(x == 5)
    with pytest.raises(ArgumentError):
        m3.array_bytes(x, 0, 1)
    assert main_tm().symbol("nope") is None
    with pytest.raises(SortMismatch):
        BitVecVal(1, 8) + BitVecVal(3, 16)
    # the engine holds bit-vectors, floats, rounding modes and declared sorts in arrays, not Bools
    with pytest.raises(Unsupported):
        ArraySort(BitVecSort(4), BoolSort())
    # 16-bit elements, little-endian bytes per element
    words = Array("words", BitVecSort(8), BitVecSort(16))
    m4 = _model(words[0] == 0x1234)
    assert m4.array_bytes(words, 0, 2) == b"\x34\x12\x00\x00" and m4[words].as_bytes(0, 1) == b"\x34\x12"
    # a count whose bytes no bytes object can hold is refused before anything is written
    huge = Array("huge", BitVecSort(64), BitVecSort(64))
    m5 = _model(huge[0] == 1)
    for count in (2**61, 2**60):
        with pytest.raises(OverflowError):
            m5.array_bytes(huge, 0, count)


def test_function_values():
    B8 = BitVecSort(8)
    f = Function("f", B8, B8)
    g = Function("g", B8, B8, BoolSort())
    x, y = BitVecs("x y", 8)
    m = _model(f(x) != f(y), g(x, f(x)), x == 3, f(3) == 9)
    fi = m[f]
    assert isinstance(fi, FuncInterp) and fi.arity() == 1 and fi.num_entries() >= 1 and len(fi) == fi.num_entries()
    entries = fi.entries()
    assert list(fi) == entries and all(len(args) == 1 for args, _ in entries)
    assert {args[0].as_long(): val.as_long() for args, val in entries}[3] == 9
    e = fi.entry(0)
    assert e.num_args() == 1 and e.arg_value(0).is_value() and e.value().is_value() and e.as_tuple() == entries[0]
    assert isinstance(fi.else_value(), BitVecNumRef)
    assert fi(3).as_long() == 9 and fi(BitVecVal(3, 8)).as_long() == 9
    assert fi(200).as_long() == fi.else_value().as_long() or fi(200).is_value()
    with pytest.raises(ArgumentError):
        fi(1, 2)
    ite = fi.as_ite(x)
    assert isinstance(ite, BitVecRef) and (ite.kind() in (Kind.ITE, Kind.VALUE))
    assert m.eval(f(3)).as_long() == 9 and m.eval(f(y)).as_long() != 9
    assert m.eval(f) is not None and m[f] is not None
    gi = m[g]
    assert gi.arity() == 2 and bool(gi(3, 9)) is True and bool(gi.else_value()) in (True, False)
    assert "else" in repr(gi) and "->" in repr(gi)
    h = Function("h", B8, B8)
    with pytest.raises(KeyError):
        m[h]
    with pytest.raises(KeyError):
        m[h(x)]  # an application of a function the solver never saw
    assert m.eval(h).num_entries() == 0 and m.eval(h(x)).as_long() == 0
    assert f in m.decls() and "f" in str(m)


def test_array_substituted_by_elimination():
    # a table of 256 constants looked up at a byte read once: elimination
    # substitutes the input by a write over a fresh array, which the model
    # used to refuse
    inp = Array("input", BitVecSort(32), BitVecSort(8))
    table = Array("table", BitVecSort(32), BitVecSort(8))
    for i in range(256):
        table = Store(table, BitVecVal(i, 32), BitVecVal((i * 7) & 0xFF, 8))
    byte = inp[BitVecVal(0, 32)]
    lookup = table[Concat(BitVecVal(0, 24), byte)]
    m = _model(lookup == 0)
    assert m.eval(lookup == 0) is BoolVal(True) and m.eval(byte).as_long() == 0
    assert m[inp][0].as_long() == 0


def test_uninterpreted_values():
    S = DeclareSort("S")
    p, q, r = Consts("p q r", S)
    m = _model(p != q, q == r)
    assert isinstance(m[p], UninterpretedNumRef) and m[p].index != m[q].index and m[q].index == m[r].index
    assert m[p].sort() is S and m[p].is_value() and m.eval(p == q) is BoolVal(False)
    assert "S!" in repr(m[p])
    t = Const("t", S)
    assert isinstance(m.eval(t), UninterpretedNumRef)


def test_functions_over_declared_sorts():
    U = DeclareSort("U")
    u, v = Consts("u v", U)
    k = Function("k", U, U)
    h = Function("h", U, BitVecSort(4))
    m = _model(u == k(k(u)), u != k(u), h(u) == 5, h(v) == 9)
    assert m.eval(u == k(k(u))) is BoolVal(True) and m.eval(u != k(u)) is BoolVal(True)
    assert m.eval(h(u)).as_long() == 5 and m.eval(h(v)).as_long() == 9
    ku = m.eval(k(u))
    assert isinstance(ku, UninterpretedNumRef) and ku.sort() is U
    ki = m[k]
    assert all(args[0].sort() is U and val.sort() is U for args, val in ki.entries())
    assert ki.else_value().sort() is U
    assert all(args[0].sort() is U for args, _ in m[h].entries())
    assert "#x" not in [line for line in m.to_smt2().splitlines() if "define-fun k " in line][0]


def test_model_printing():
    x, y = BitVecs("x y", 8)
    a = FP("a", Float32())
    m = _model(x == 5, y == 7, fpEQ(a, 1.5))
    s = str(m)
    assert s.startswith("[") and s.endswith("]") and "x = 5" in s and "y = 7" in s and "a = 1.5" in s
    text = repr(m)
    assert text == m.to_smt2() == m.sexpr()
    assert "(define-fun x () (_ BitVec 8) #x05)" in text.replace("  ", " ")
    assert "(define-fun a () (_ FloatingPoint 8 24) (fp #b0 #b01111111 #b10000000000000000000000))" in text


def test_model_pickle_and_translate():
    B8 = BitVecSort(8)
    x, y = BitVecs("x y", 8)
    a = Array("a", BitVecSort(32), BitVecSort(8))
    f = Function("f", B8, B8)
    fa = FP("fa", Float32())
    r = Real("r")
    p = Bool("p")
    rm = Const("rm", RoundingModeSort())
    S = DeclareSort("S")
    u, v = Consts("u v", S)
    m = _model(x == 5, y == 7, f(x) == 9, f(1) == 2, a[3] == 4, fpEQ(fa, 1.5), r == Q(1, 3), p, rm == RTP(), u != v)
    data = pickle.dumps(m)
    m2 = pickle.loads(data)
    assert isinstance(m2, Model) and m2.manager() is not m.manager()  # a private manager
    assert m2[x].as_long() == 5 and m2[y].as_long() == 7  # keys are translated by name
    assert m2.eval(x + y).as_long() == 12
    assert m2[f](5).as_long() == 9 and m2[f](1).as_long() == 2
    assert m2[a][3].as_long() == 4 and m2[a].default.as_long() == 0
    assert float(m2[fa]) == 1.5 and m2[r].as_fraction() == Fraction(1, 3)
    assert bool(m2[p]) is True and m2[rm].as_rounding_mode() == RoundingMode.RTP
    assert m2[u].index != m2[v].index
    assert str(m2).count("=") >= 8 and m2.to_smt2().count("define-fun") == m.to_smt2().count("define-fun")
    # pickling the pickled model again round-trips
    m3 = pickle.loads(pickle.dumps(m2))
    assert m3[x].as_long() == 5
    # translate onto a manager of our own
    tm2 = TermManager()
    m4 = m.translate(tm2)
    assert m4.manager() is tm2 and m4[BitVec("x", 8, tm=tm2)].as_long() == 5 and m4[x].as_long() == 5
    assert m.translate(main_tm()) is m
    # from_smt2 onto a manager with a live solver builds the model through a scratch
    # solver of its own; the live solver is untouched
    s = Solver()
    s.add(x == 1)
    m5 = Model.from_smt2(m.to_smt2(), main_tm())
    assert m5.manager() is main_tm() and m5[x].as_long() == 5 and m5[f](5).as_long() == 9
    assert s.check() == sat and s.model()[x].as_long() == 1 and len(s.assertions()) == 1
    s.close()
    m6 = Model.from_smt2(m.to_smt2(), main_tm())  # no live solver: the same
    assert m6.manager() is main_tm() and m6[x].as_long() == 5
    with pytest.raises(TypeError):
        Model.from_smt2("()", 3)
    with pytest.raises(ParseError):
        Model.from_smt2("(define-fun x () (_ BitVec 8) nonsense)")


@pytest.mark.parametrize("sort_name", ["S", "sort with spaces"])
def test_model_pickle_uninterpreted_values(sort_name):
    p, q, r = Consts("p q r", DeclareSort(sort_name))
    m = _model(p == q, p != r)
    for rebuilt in (pickle.loads(pickle.dumps(m)), m.translate(TermManager())):
        assert rebuilt[p].index == rebuilt[q].index
        assert rebuilt[p].index != rebuilt[r].index
        assert bool(rebuilt.eval(p == q)) and bool(rebuilt.eval(p != r))


@pytest.mark.parametrize("sort_name, sort_text, first, second", [
    ("S", "S", "S!0", "S!1"),
    ("sort with spaces", "|sort with spaces|", "|sort with spaces!0|", "|sort with spaces!1|"),
    ("S", "|S|", "(as |@S!0| S)", "(as @S!1 |S|)"),
])
def test_model_read_uninterpreted_values(sort_name, sort_text, first, second):
    # Older pickles store bare S!k values; quoted and simple symbols name the
    # same sort and abstract values in the qualified spelling.
    text = """(
      (define-fun p () {sort} {first})
      (define-fun q () {sort} {first})
      (define-fun r () {sort} {second})
    )""".format(sort=sort_text, first=first, second=second)
    m = Model.from_smt2(text)
    p, q, r = Consts("p q r", DeclareSort(sort_name, tm=m.manager()))
    assert m[p].index == m[q].index
    assert m[p].index != m[r].index


@pytest.mark.parametrize("qualifier", ["T", "(_ BitVec 8)"])
def test_model_read_uninterpreted_value_wrong_sort(qualifier):
    with pytest.raises(ParseError, match="cannot read"):
        Model.from_smt2("(define-fun p () S (as @S!0 %s))" % qualifier)


def test_model_survives_solver_changes():
    x = BitVec("x", 8)
    s = Solver()
    s.add(x == 1)
    assert s.check() == sat
    m = s.model()
    s.push()
    s.add(x == 2)
    assert s.check() == unsat
    with pytest.raises(NoModel):
        s.model()
    s.pop()
    assert m[x].as_long() == 1  # detached
    assert s.value(x).as_long() == 1 if s.check() == sat else True
    s.close()
    assert m[x].as_long() == 1
    assert m.eval(x + 1).as_long() == 2


def test_solver_value_and_candidate():
    x = BitVec("x", 8)
    s = Solver()
    s.add(ULT(x, 2))
    assert s.check() == sat
    assert s.value(x).as_long() < 2 and s.value(x) is s.model()[x]
    with pytest.raises(KeyError):
        s.value(BitVec("other", 8))
    s.add(x == 5)
    assert s.check() == unsat and s.candidate_model() is None
    s.close()
