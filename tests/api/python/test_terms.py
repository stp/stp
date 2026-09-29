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

"""Sorts, the ExprRef family, the operator ledger, literal
strictness and every builder at least once."""

import pickle
from fractions import Fraction

import pytest

from stp import *
import stp


# ---------------------------------------------------------------- manager


def test_term_manager_basics(fresh_manager):
    tm = fresh_manager
    assert main_tm() is tm
    assert tm.simplify is True
    assert tm.default_rounding_mode == RoundingMode.RNE
    tm.default_rounding_mode = RoundingMode.RTZ
    assert tm.default_rounding_mode == RoundingMode.RTZ
    assert tm.id > 0
    other = TermManager(simplify=False, default_rounding_mode=RoundingMode.RTP)
    assert other.simplify is False and other.default_rounding_mode == RoundingMode.RTP
    assert other.id != tm.id
    # manager entries by name through Options
    third = TermManager(options=Options(uf_sort_width=8, simplify=False))
    assert third.uf_sort_width == 8 and third.simplify is False
    with pytest.raises(OptionError):
        TermManager(options=Options(max_time=5))  # solver-scoped
    with pytest.raises(TypeError):
        set_main_tm(object())


def test_name_table_and_symbols(fresh_manager):
    tm = fresh_manager
    x = BitVec("x", 8)
    assert tm.declare("x", BitVecSort(8)) is x
    assert BitVec("x", 8) is x
    with pytest.raises(SortMismatch):
        Bool("x")  # the name is taken at another sort
    assert tm.symbol("x") is x
    assert tm.symbol("nope") is None
    tm.bind_symbol("alias", x)
    assert tm.symbol("alias") is x
    s = Solver()  # the alias names x for the parsers too
    s.from_string("(assert (= alias #x05))")
    assert s.check() == sat and s.model()[x].as_long() == 5
    s.close()
    # a name SMT-LIB predefines cannot be told apart from the predefined symbol
    for name in ("select", "true", "bvadd", "RNE", "+"):
        with pytest.raises(ArgumentError):
            BitVec(name, 8)
        with pytest.raises(ArgumentError):
            tm.bind_symbol(name, x)
    with pytest.raises(ArgumentError):
        tm.declare_sort("Bool")
    assert BitVec("Select", 8).decl_name() == "Select"
    assert x in tm.symbols()
    f = tm.mk_fresh(BitVecSort(8), "c")
    assert f.is_symbol() and f.decl_name().startswith("c!")
    assert tm.symbol(f.decl_name()) is None  # anonymous: never in the name table
    assert tm.term_from_id(x.id) is x
    with pytest.raises(ArgumentError):
        tm.term_from_id(1 << 62)
    # an id does not keep its term: once the last wrapper goes, it resolves no more
    t = x * 123
    tid = t.id
    del t
    with pytest.raises(ArgumentError):
        tm.term_from_id(tid)
    S = tm.declare_sort("S")
    assert S in tm.declared_sorts() and DeclareSort("S") is S
    T = tm.mk_fresh_sort("T")
    assert T.kind() == SortKind.UNINTERPRETED and T is not S
    t = tm.mk_term(Kind.BV_ADD, [x, BitVecVal(1, 8)])
    assert t.kind() == Kind.BV_ADD
    assert tm.simplify_term(x + 0) is x


# ---------------------------------------------------------------- sorts


def test_sorts():
    b, bv, fp, rm, real = BoolSort(), BitVecSort(32), FPSort(8, 24), RoundingModeSort(), RealSort()
    assert (b.kind(), bv.kind(), fp.kind(), rm.kind(), real.kind()) == (
        SortKind.BOOL, SortKind.BV, SortKind.FP, SortKind.RM, SortKind.REAL)
    assert bv.size() == 32 and fp.ebits() == 8 and fp.sbits() == 24
    assert Float16() == FPSort(5, 11) and Float32() == fp and Float64() == FPSort(11, 53) and Float128() == FPSort(15, 113)
    assert FloatHalf() is Float16() and FloatSingle() is Float32() and FloatDouble() is Float64() and FloatQuadruple() is Float128()
    assert BitVecSort(32) is bv and BitVecSort(32) == bv and bv != BitVecSort(8)
    assert hash(bv) == hash(BitVecSort(32))
    assert repr(bv) == "BitVecSort(32)" and repr(fp) == "FPSort(8, 24)" and repr(b) == "BoolSort()"
    assert bv.sexpr() == "(_ BitVec 32)" and fp.sexpr() == "(_ FloatingPoint 8 24)"
    A = ArraySort(bv, BitVecSort(8))
    assert A.kind() == SortKind.ARRAY and A.domain() is bv and A.range() == BitVecSort(8)
    assert repr(A) == "ArraySort(BitVecSort(32), BitVecSort(8))"
    F = FuncSort(bv, BitVecSort(8), b)
    assert F.kind() == SortKind.FUN and F.arity() == 2 and F.domain(1) == BitVecSort(8) and F.range() is b
    with pytest.raises(IndexError):
        F.domain(2)
    S = DeclareSort("S")
    assert S.kind() == SortKind.UNINTERPRETED and S.name() == "S" and DeclareSort("S") is S
    assert FreshSort("Q") is not FreshSort("Q")
    assert bv.manager() is main_tm()
    assert not (bv == 32)  # not a sort: identity answer
    with pytest.raises(ArgumentError):
        BitVecSort(0)
    with pytest.raises(TypeError):
        ArraySort(bv, 8)
    assert isinstance(bv, BitVecSortRef) and isinstance(A, ArraySortRef) and isinstance(F, FuncSortRef)
    assert isinstance(S, UninterpretedSortRef) and isinstance(b, BoolSortRef) and isinstance(rm, RMSortRef)
    assert isinstance(real, RealSortRef) and isinstance(fp, FPSortRef)
    assert pickle.loads(pickle.dumps(A)) is A and pickle.loads(pickle.dumps(S)) is S
    assert is_sort(bv) and not is_sort(BitVec("x", 8))


# ---------------------------------------------------------------- declarations and values


def test_declarations():
    p, q = Bools("p q")
    assert isinstance(p, BoolRef) and p.sort() == BoolSort() and p.decl_name() == "p"
    x, y = BitVecs("x y", 8)
    assert isinstance(x, BitVecRef) and x.size() == 8
    assert [t.decl_name() for t in BitVecs(["a1", "a2"], 4)] == ["a1", "a2"]
    a = FP("a", Float32())
    assert isinstance(a, FPRef) and a.ebits() == 8 and a.sbits() == 24
    assert len(FPs("f1 f2", Float64())) == 2
    r = Real("r")
    assert isinstance(r, RealRef) and len(Reals("r1 r2")) == 2
    arr = Array("arr", BitVecSort(32), BitVecSort(8))
    assert isinstance(arr, ArrayRef) and arr.domain() == BitVecSort(32) and arr.range() == BitVecSort(8)
    f = Function("f", BitVecSort(8), BitVecSort(8), BoolSort())
    assert isinstance(f, FuncRef) and f.arity() == 2 and f.range() == BoolSort() and f.domain(0) == BitVecSort(8)
    rm = Const("rm", RoundingModeSort())
    assert isinstance(rm, RMRef)
    S = DeclareSort("S")
    c1, c2 = Consts("c1 c2", S)
    assert isinstance(c1, UninterpretedRef) and c1.sort() is S
    fc = FreshConst(BitVecSort(8), "k")
    assert fc.decl_name().startswith("k!") and FreshConst(BitVecSort(8), "k") is not fc
    assert FreshBool().sort() == BoolSort() and FreshBitVec(4).size() == 4
    assert x.kind() == Kind.CONSTANT and x.is_symbol() and not x.is_value() and x.num_args() == 0
    assert x.manager() is main_tm() and x.id > 0


def test_values():
    assert BoolVal(True).kind() == Kind.VALUE and bool(BoolVal(True)) is True and bool(BoolVal(False)) is False
    assert isinstance(BoolVal(True), BoolNumRef) and is_true(BoolVal(True)) and is_false(BoolVal(False))
    v = BitVecVal(5, 8)
    assert isinstance(v, BitVecNumRef) and v.as_long() == 5 and v.as_signed_long() == 5 and int(v) == 5
    assert v.as_binary_string() == "00000101" and v.as_hex_string() == "05" and v.as_string() == "5"
    assert BitVecVal(-2, 8).as_long() == 254 and BitVecVal(-2, 8).as_signed_long() == -2
    assert BitVecVal(0x1234, 16).as_bytes() == b"\x34\x12" and BitVecVal(0x1234, 16).as_bytes("big") == b"\x12\x34"
    assert BitVecVal(5, BitVecSort(8)) is v
    assert [0] * 3 == [0, 0, 0] and [1, 2][BitVecVal(1, 8)] == 2  # __index__
    big = BitVecVal((1 << 100) + 5, 128)
    assert big.as_long() == (1 << 100) + 5 and big.as_signed_long() == (1 << 100) + 5
    assert BitVecVal(-(1 << 100), 128).as_signed_long() == -(1 << 100)
    assert BitVecVal(-1, 128).as_long() == (1 << 128) - 1
    assert repr(v) == "#x05" and str(v) == "5"
    # rounding modes
    assert RNE().as_rounding_mode() == RoundingMode.RNE and RTZ().as_rounding_mode() == RoundingMode.RTZ
    assert RNA().as_rounding_mode() == RoundingMode.RNA and RTP().as_rounding_mode() == RoundingMode.RTP
    assert RTN().as_rounding_mode() == RoundingMode.RTN and RMVal(RoundingMode.RTZ) is RTZ()
    assert RoundNearestTiesToEven() is RNE() and RoundTowardZero() is RTZ() and RoundTowardPositive() is RTP()
    assert RoundTowardNegative() is RTN() and RoundNearestTiesToAway() is RNA()
    assert isinstance(RNE(), RMNumRef) and is_rm(RNE())
    # reals
    third = Q(1, 3)
    assert isinstance(third, RatNumRef) and third.as_fraction() == Fraction(1, 3)
    assert third.numerator() == 1 and third.denominator() == 3 and third.numerator_as_long() == 1
    assert third.as_decimal(4) == "0.3333?" and Q(3, 4).as_decimal(3) == "0.750" and float(Q(1, 4)) == 0.25
    # float() of a Real is correctly rounded, and past the double range raises as float() of an int does
    with pytest.raises(OverflowError):
        float(RealVal(10**400))
    assert float(Q(1, 10**400)) == 0.0 and float(Q(10**400 + 1, 10**400)) == 1.0
    assert float(Q(2**1100 + 1, 2**100)) == 1.0715086071862673e+301
    assert float(Q(244256145482930251, 8496936760652861)) == 28.746376766509307
    assert RealVal("0.25").as_fraction() == Fraction(1, 4) and RealVal(7).as_string() == "7"
    assert RealVal(Fraction(-3, 7)).as_string() == "-3/7" and RealVal("-3/7").as_fraction() == Fraction(-3, 7)
    assert RealVal(third) is third
    with pytest.raises(TypeError):
        RealVal(1.5)
    with pytest.raises(TypeError):
        Q(1.0, 2)


def test_fp_values():
    v = FPVal(1.5, Float32())
    assert isinstance(v, FPNumRef) and float(v) == 1.5 and v.bits() == 0x3FC00000
    assert v.sign() is False and v.exponent() == 127 and v.exponent(biased=False) == 0
    assert v.significand() == 1 << 22 and v.significand_as_long() == v.significand()
    assert v.isNormal() and not v.isNaN() and not v.isInf() and not v.isZero() and not v.isSubnormal()
    assert v.isPositive() and not v.isNegative() and v.as_fraction() == Fraction(3, 2)
    assert v.as_string() == "(fp #b0 #b01111111 #b10000000000000000000000)" and repr(v) == v.as_string()
    assert str(v) == "1.5"
    assert FPVal(3, Float32()) is FPVal(3.0, Float32())
    assert FPVal("0.1", Float64()).as_fraction() == Fraction(0.1)
    assert FPVal(Fraction(1, 4), Float32()).as_fraction() == Fraction(1, 4)
    # a decimal literal is rounded once under the given mode
    assert FPVal("0.1", Float32(), RoundingMode.RTZ).as_fraction() < Fraction(1, 10) < FPVal("0.1", Float32(), RTP()).as_fraction()
    assert fpNaN(Float32()).isNaN() and fpPlusInfinity(Float32()).isInf() and fpMinusInfinity(Float32()).isNegative()
    assert fpInfinity(Float32(), True) is fpMinusInfinity(Float32())
    assert fpPlusZero(Float32()).isZero() and fpMinusZero(Float32()).isNegative() and fpZero(Float32(), False) is fpPlusZero(Float32())
    with pytest.raises(NotAValue):
        fpNaN(Float32()).as_fraction()
    with pytest.raises(NotAValue):
        fpPlusInfinity(Float32()).as_fraction()
    assert fpFromBits(0x3F800000, Float32()) is FPVal(1.0, Float32())
    assert fpFromBits(BitVecVal(0x3F800000, 32), Float32()) is FPVal(1.0, Float32())
    with pytest.raises(ArgumentError):
        fpFromBits(1 << 40, Float32())
    one = fpFP(BitVecVal(0, 1), BitVecVal(127, 8), BitVecVal(0, 23))
    assert one is FPVal(1.0, Float32())
    with pytest.raises(DoesNotFit):
        float(FPVal(1.0, Float128()))
    assert FPVal(1.0, Float128()).as_fraction() == 1
    assert FPVal(1e-45, Float32()).isSubnormal()
    with pytest.raises(TypeError):
        FPVal(True, Float32())
    with pytest.raises(SortMismatch):
        FPVal(v, Float64())


def test_literal_strictness():
    with pytest.raises(ArgumentError) as e:
        BitVecVal(256, 8)
    assert e.value.code == ErrorCode.VALUE_OUT_OF_RANGE and isinstance(e.value, ValueError)
    with pytest.raises(ArgumentError):
        BitVecVal(-129, 8)
    assert BitVecVal(256, 8, wrap=True).as_long() == 0
    assert BitVecVal(-129, 8, wrap=True).as_long() == 127
    assert BitVecVal(-1, 8).as_long() == 255  # the two's complement range is fine
    assert BitVecVal(255, 8).as_long() == 255
    x = BitVec("x", 8)
    with pytest.raises(ArgumentError):
        x + 300
    with pytest.raises(ArgumentError):
        x == -200
    with pytest.raises(TypeError):
        x + 1.5
    with pytest.raises(TypeError):
        x == 1.5
    with pytest.raises(TypeError):
        BitVecVal(1.0, 8)
    r = Real("r")
    with pytest.raises(TypeError):
        r * 0.5
    with pytest.raises(TypeError):
        0.5 + r
    assert (r * Fraction(1, 2)).kind() == Kind.REAL_MUL


# ---------------------------------------------------------------- the operator ledger


def test_equality_builds_terms():
    x, y = BitVecs("x y", 8)
    e = x == y
    assert isinstance(e, BoolRef) and e.kind() == Kind.EQUAL
    d = x != y
    assert d.kind() == Kind.DISTINCT
    assert (x == 3).kind() == Kind.EQUAL and (3 == x).kind() == Kind.EQUAL
    a = FP("a", Float32())
    assert (a == 1.5).kind() == Kind.EQUAL  # SMT '=', not fp.eq
    assert fpEQ(a, FP("b", Float32())).kind() == Kind.FP_EQ
    assert (Real("r") == 1).kind() == Kind.EQUAL
    arr = Array("arr", BitVecSort(32), BitVecSort(8))
    assert (arr == Array("brr", BitVecSort(32), BitVecSort(8))).kind() == Kind.EQUAL
    assert (x == None) is False and (x != None) is True  # noqa: E711
    assert (x == "str") is False and (x == object()) is False
    assert x.eq(x) and not x.eq(y) and not x.eq(3)
    assert x is BitVec("x", 8) and hash(x) == hash(BitVec("x", 8))
    assert {x: 1}[BitVec("x", 8)] == 1 and x in {x, y}
    with pytest.raises(TypeError):
        bool(x == y)
    assert bool(BitVecVal(3, 8) == 3) is True and bool(BitVecVal(3, 8) == 4) is False
    # a ground conversion folds; an unspecified case does not: which zero fp.min(+0, -0) is,
    # or what fp.to_ubv of NaN is, is a check's to choose
    assert bool(fpToSBV(RTZ(), FPVal(2.5, Float16()), BitVecSort(8)) == 2) is True
    with pytest.raises(TypeError):
        bool(fpMin(fpPlusZero(Float16()), fpMinusZero(Float16())) == fpPlusZero(Float16()))
    with pytest.raises(TypeError):
        bool(fpToUBV(RTZ(), fpNaN(Float16()), BitVecSort(8)) == 5)
    with pytest.raises(TypeError):
        bool(x)
    assert x in [x]  # identity short-circuits the list search
    with pytest.raises(TypeError):
        y in [x]  # ... but an absent term compares with ==, whose result has no truth value
    with pytest.raises(TypeError):
        sorted([x, y])
    with pytest.raises(TypeError):
        not Bool("p")
    with pytest.raises(TypeError):
        iter(x)
    with pytest.raises(TypeError):
        x[0]
    other = TermManager()
    z = BitVec("z", 8, tm=other)
    with pytest.raises(SortMismatch):
        x == z
    # a Python bool condition is built in the branches' manager
    assert If(True, z, 0)._manager() is other and simplify(If(False, 0, z)) is z


def test_bv_operators():
    set_main_tm(TermManager(simplify=False))  # kinds are exact only without construction-time folding
    x, y = BitVecs("x y", 8)
    assert (x + y).kind() == Kind.BV_ADD and (x - y).kind() == Kind.BV_SUB and (x * y).kind() == Kind.BV_MUL
    assert (x & y).kind() == Kind.BV_AND and (x | y).kind() == Kind.BV_OR and (x ^ y).kind() == Kind.BV_XOR
    assert (~x).kind() == Kind.BV_NOT and (-x).kind() == Kind.BV_NEG and (+x) is x
    assert (x << y).kind() == Kind.BV_SHL and (x << 2).kind() == Kind.BV_SHL and (1 << x).kind() == Kind.BV_SHL
    assert (1 + x).kind() == Kind.BV_ADD and (1 - x).kind() == Kind.BV_SUB and (2 * x).kind() == Kind.BV_MUL
    assert (1 & x).kind() == Kind.BV_AND and (1 | x).kind() == Kind.BV_OR and (1 ^ x).kind() == Kind.BV_XOR
    # signed comparisons and arithmetic shift (z3py)
    assert (x < y).kind() in (Kind.BV_SLT, Kind.BV_SGT) and (x <= y).kind() in (Kind.BV_SLE, Kind.BV_SGE)
    assert (x > y).kind() in (Kind.BV_SGT, Kind.BV_SLT) and (x >= y).kind() in (Kind.BV_SGE, Kind.BV_SLE)
    assert (x >> y).kind() == Kind.BV_ASHR and (1 >> x).kind() == Kind.BV_ASHR
    assert ULT(x, y).kind() == Kind.BV_ULT and ULE(x, y).kind() == Kind.BV_ULE
    assert UGT(x, y).kind() in (Kind.BV_UGT, Kind.BV_ULT) and UGE(x, y).kind() in (Kind.BV_UGE, Kind.BV_ULE)
    assert LShR(x, y).kind() == Kind.BV_LSHR and LShR(x, 3).kind() in (Kind.BV_LSHR, Kind.BV_CONCAT)
    assert SLT(x, y).kind() in (Kind.BV_SLT, Kind.BV_SGT) and SGE(x, y).kind() in (Kind.BV_SGE, Kind.BV_SLE)
    assert UDiv(x, y).kind() == Kind.BV_UDIV and URem(x, y).kind() == Kind.BV_UREM
    assert SDiv(x, y).kind() == Kind.BV_SDIV and SRem(x, y).kind() == Kind.BV_SREM and SMod(x, y).kind() == Kind.BV_SMOD
    for op in (lambda: x / y, lambda: x // y, lambda: x % y, lambda: x / 2, lambda: 2 / x, lambda: x % 2, lambda: x ** 2):
        with pytest.raises(TypeError):
            op()
    # simplification keeps values exact
    assert simplify(BitVecVal(200, 8) + 100).as_long() == 44
    assert simplify(BitVecVal(7, 8) >> 1).as_long() == 3 and simplify(BitVecVal(-8, 8) >> 1).as_signed_long() == -4
    assert simplify(LShR(BitVecVal(-8, 8), 1)).as_long() == 124
    assert simplify(BitVecVal(1, 8) << 3).as_long() == 8
    assert bool(simplify(BitVecVal(-1, 8) < 0)) and bool(simplify(ULT(1, BitVecVal(-1, 8))))
    assert simplify(UDiv(BitVecVal(7, 8), 2)).as_long() == 3 and simplify(SDiv(BitVecVal(-7, 8), 2)).as_signed_long() == -3
    assert simplify(URem(BitVecVal(7, 8), 3)).as_long() == 1 and simplify(SRem(BitVecVal(-7, 8), 3)).as_signed_long() == -1
    assert simplify(SMod(BitVecVal(-7, 8), 3)).as_signed_long() == 2


def test_bv_structure_builders():
    set_main_tm(TermManager(simplify=False))
    x, y = BitVecs("x y", 8)
    e = Extract(3, 0, x)
    assert e.kind() == Kind.BV_EXTRACT and e.indices() == [3, 0] and e.size() == 4 and e.num_args() == 1 and e.arg(0) is x
    assert Concat(x, y).size() == 16 and Concat([x, y, x]).size() == 24 and Concat(x) is x
    assert simplify(Concat(BitVecVal(1, 8), BitVecVal(2, 8))).as_long() == 0x0102
    assert ZeroExt(8, x).size() == 16 and SignExt(8, x).size() == 16
    assert simplify(ZeroExt(8, BitVecVal(255, 8))).as_long() == 255 and simplify(SignExt(8, BitVecVal(255, 8))).as_long() == 0xFFFF
    assert RepeatBitVec(3, x).size() == 24 and RepeatBV is RepeatBitVec
    assert RotateLeft(x, 3).size() == 8 and RotateRight(x, 3).size() == 8 and RotateLeft(x, y).size() == 8
    assert simplify(RotateLeft(BitVecVal(0x81, 8), 1)).as_long() == 0x03
    assert simplify(RotateRight(BitVecVal(0x81, 8), 1)).as_long() == 0xC0
    assert simplify(RotateLeft(BitVecVal(0x81, 8), BitVecVal(1, 8))).as_long() == 0x03
    assert simplify(RotateRight(BitVecVal(0x81, 8), BitVecVal(1, 8))).as_long() == 0xC0
    # a term amount is taken modulo the size, as an int amount is
    for k in range(0, 20):
        for rotate in (RotateLeft, RotateRight):
            assert simplify(rotate(BitVecVal(0x81, 8), BitVecVal(k, 8))).as_long() == \
                simplify(rotate(BitVecVal(0x81, 8), k)).as_long(), (rotate.__name__, k)
    s = Solver()
    s.add(RotateLeft(y, BitVecVal(9, 8)) != RotateLeft(y, 1))
    assert s.check() == unsat
    assert bool(simplify(Bit(BitVecVal(4, 8), 2))) and not bool(simplify(Bit(BitVecVal(4, 8), 1)))
    assert simplify(BoolToBV1(BoolVal(True))).as_long() == 1 and bool(simplify(BV1ToBool(BitVecVal(1, 1))))
    assert simplify(BVComp(BitVecVal(3, 8), 3)).as_long() == 1 and simplify(BVComp(x, x)).as_long() == 1
    assert simplify(BVNand(BitVecVal(0xFF, 8), 0xFF)).as_long() == 0 and simplify(BVNor(BitVecVal(0, 8), 0)).as_long() == 0xFF
    assert simplify(BVXnor(BitVecVal(0xF0, 8), 0xF0)).as_long() == 0xFF
    assert simplify(BVRedAnd(BitVecVal(0xFF, 8))).as_long() == 1 and simplify(BVRedOr(BitVecVal(0, 8))).as_long() == 0
    assert BVRedAnd(x).size() == 1 and BVRedOr(x).size() == 1
    with pytest.raises(ArgumentError):
        Extract(9, 0, x)
    with pytest.raises(TypeError):
        Extract(3, 0, Bool("p"))


def test_overflow_predicates():
    x, y = BitVecs("x y", 8)
    for f in (bvuaddo, bvsaddo, bvumulo, bvsmulo, bvusubo, bvssubo, bvsdivo):
        assert isinstance(f(x, y), BoolRef)
    assert isinstance(bvnego(x), BoolRef)
    assert bool(simplify(bvuaddo(BitVecVal(200, 8), 100))) and not bool(simplify(bvuaddo(BitVecVal(1, 8), 1)))
    assert bool(simplify(bvsaddo(BitVecVal(100, 8), 100))) and bool(simplify(bvumulo(BitVecVal(16, 8), 16)))
    assert bool(simplify(bvsmulo(BitVecVal(-128, 8), -1))) and bool(simplify(bvusubo(BitVecVal(0, 8), 1)))
    assert bool(simplify(bvssubo(BitVecVal(-128, 8), 1))) and bool(simplify(bvnego(BitVecVal(-128, 8))))
    assert bool(simplify(bvsdivo(BitVecVal(-128, 8), -1)))
    # the z3py names, as negations
    assert bool(simplify(BVAddNoOverflow(BitVecVal(1, 8), 1, False))) and not bool(simplify(BVAddNoOverflow(BitVecVal(200, 8), 100, False)))
    assert not bool(simplify(BVAddNoOverflow(BitVecVal(100, 8), 100, True))) and bool(simplify(BVAddNoOverflow(BitVecVal(-100, 8), -100, True)))
    assert not bool(simplify(BVAddNoUnderflow(BitVecVal(-100, 8), -100))) and bool(simplify(BVAddNoUnderflow(BitVecVal(100, 8), 100)))
    assert not bool(simplify(BVSubNoOverflow(BitVecVal(100, 8), -100))) and bool(simplify(BVSubNoOverflow(BitVecVal(1, 8), 1)))
    assert not bool(simplify(BVSubNoUnderflow(BitVecVal(0, 8), 1, False))) and bool(simplify(BVSubNoUnderflow(BitVecVal(1, 8), 1, False)))
    assert not bool(simplify(BVSubNoUnderflow(BitVecVal(-100, 8), 100, True))) and bool(simplify(BVSubNoUnderflow(BitVecVal(100, 8), -20, True)))
    assert not bool(simplify(BVMulNoOverflow(BitVecVal(16, 8), 16, False))) and bool(simplify(BVMulNoOverflow(BitVecVal(4, 8), 4, False)))
    assert not bool(simplify(BVMulNoOverflow(BitVecVal(64, 8), 2, True))) and bool(simplify(BVMulNoOverflow(BitVecVal(-64, 8), 2, True)))
    assert not bool(simplify(BVMulNoUnderflow(BitVecVal(-64, 8), 3))) and bool(simplify(BVMulNoUnderflow(BitVecVal(64, 8), 2)))
    assert not bool(simplify(BVSNegNoOverflow(BitVecVal(-128, 8)))) and bool(simplify(BVSNegNoOverflow(BitVecVal(5, 8))))
    assert not bool(simplify(BVSDivNoOverflow(BitVecVal(-128, 8), -1))) and bool(simplify(BVSDivNoOverflow(BitVecVal(-128, 8), 2)))


def test_bool_operators():
    set_main_tm(TermManager(simplify=False))
    p, q, r = Bools("p q r")
    assert (~p).kind() == Kind.NOT and (p & q).kind() == Kind.AND and (p | q).kind() == Kind.OR and (p ^ q).kind() == Kind.XOR
    assert (True & p).kind() in (Kind.AND, Kind.CONSTANT) and (p | False).kind() in (Kind.OR, Kind.CONSTANT)
    assert Not(p).kind() == Kind.NOT and And(p, q, r).kind() == Kind.AND and Or([p, q]).kind() == Kind.OR
    assert And(p, [q, r]).num_args() == 3 and Xor(p, q).kind() == Kind.XOR and Implies(p, q).kind() in (Kind.IMPLIES, Kind.OR)
    assert And(p) is p and bool(And()) is True and bool(Or()) is False
    assert bool(simplify(And(True, True))) and not bool(simplify(Or(False, False))) and bool(simplify(Implies(False, False)))
    assert bool(simplify(Xor(True, False))) and not bool(simplify(Not(True)))
    assert bool(Distinct(BoolVal(True), BoolVal(False))) and not bool(Not(Distinct(BoolVal(True), BoolVal(False))))
    x, y = BitVecs("x y", 8)
    i = If(p, x, y)
    assert i.kind() == Kind.ITE and i.sort() == BitVecSort(8) and If(p, x, 3).kind() == Kind.ITE
    assert simplify(If(True, x, y)) is x
    assert simplify(If(BoolVal(False), 1, BitVecVal(2, 8))).as_long() == 2
    with pytest.raises(TypeError):
        If(p, 1, 2)
    with pytest.raises(TypeError):
        And(p, x)
    d = Distinct(x, y, BitVecVal(3, 8))
    assert d.kind() == Kind.DISTINCT and d.num_args() == 3
    assert Sum(x, y, 3).kind() == Kind.BV_ADD and Product(x, y).kind() == Kind.BV_MUL and Sum(x) is x
    assert simplify(Sum(BitVecVal(1, 8), 2, 3)).as_long() == 6 and simplify(Product(BitVecVal(2, 8), 3)).as_long() == 6
    a, b = Reals("a b")
    assert Sum(a, b, 1).kind() == Kind.REAL_ADD and Product(a, 2).kind() == Kind.REAL_MUL
    with pytest.raises(TypeError):
        Sum(1, 2)
    with pytest.raises(TypeError):
        Sum(p, q)


def test_fp_operators(fresh_manager):
    fresh_manager = TermManager(simplify=False)
    set_main_tm(fresh_manager)
    a, b = FPs("a b", Float32())
    for t, k in ((a + b, Kind.FP_ADD), (a - b, Kind.FP_SUB), (a * b, Kind.FP_MUL), (a / b, Kind.FP_DIV),
                 (a + 1.5, Kind.FP_ADD), (1.5 + a, Kind.FP_ADD), (2 * a, Kind.FP_MUL), (a / 2, Kind.FP_DIV)):
        assert t.kind() == k and isinstance(t, FPRef)
        assert t.arg(0).as_rounding_mode() == RoundingMode.RNE  # the manager's default mode
    fresh_manager.default_rounding_mode = RoundingMode.RTZ
    assert (a + b).arg(0).as_rounding_mode() == RoundingMode.RTZ
    fresh_manager.default_rounding_mode = RoundingMode.RNE
    assert (-a).kind() == Kind.FP_NEG and abs(a).kind() == Kind.FP_ABS and (+a) is a
    assert (a < b).kind() in (Kind.FP_LT, Kind.FP_GT) and (a <= b).kind() in (Kind.FP_LEQ, Kind.FP_GEQ)
    assert (a > b).kind() in (Kind.FP_GT, Kind.FP_LT) and (a >= b).kind() in (Kind.FP_GEQ, Kind.FP_LEQ)
    assert (a < 0.0).kind() in (Kind.FP_LT, Kind.FP_GT)
    assert fpAbs(a).kind() == Kind.FP_ABS and fpNeg(a).kind() == Kind.FP_NEG
    t = fpAdd(RTZ(), a, 1.5)
    assert t.kind() == Kind.FP_ADD and t.arg(0).as_rounding_mode() == RoundingMode.RTZ
    assert fpAdd(RoundingMode.RTP, a, b).arg(0).as_rounding_mode() == RoundingMode.RTP
    # a literal is rounded under THIS call's mode
    assert fpAdd(RTZ(), a, 0.1).arg(2).as_fraction() == FPVal(0.1, Float32(), RoundingMode.RTZ).as_fraction()
    assert fpAdd(RTP(), a, 0.1).arg(2).as_fraction() == FPVal(0.1, Float32(), RoundingMode.RTP).as_fraction()
    assert fpSub(RNE(), a, b).kind() == Kind.FP_SUB and fpMul(RNE(), a, b).kind() == Kind.FP_MUL
    assert fpDiv(RNE(), a, b).kind() == Kind.FP_DIV and fpFMA(RNE(), a, b, a).kind() == Kind.FP_FMA
    assert fpSqrt(RNE(), a).kind() == Kind.FP_SQRT and fpRem(a, b).kind() == Kind.FP_REM
    assert fpRoundToIntegral(RTZ(), a).kind() == Kind.FP_RTI and fpMin(a, b).kind() == Kind.FP_MIN and fpMax(a, b).kind() == Kind.FP_MAX
    assert fpEQ(a, b).kind() == Kind.FP_EQ and fpNEQ(a, b).kind() == Kind.NOT
    assert fpLT(a, b).kind() in (Kind.FP_LT, Kind.FP_GT) and fpLEQ(a, b).kind() in (Kind.FP_LEQ, Kind.FP_GEQ)
    assert fpGT(a, b).kind() in (Kind.FP_GT, Kind.FP_LT) and fpGEQ(a, b).kind() in (Kind.FP_GEQ, Kind.FP_LEQ)
    for f, k in ((fpIsNaN, Kind.FP_IS_NAN), (fpIsInf, Kind.FP_IS_INF), (fpIsZero, Kind.FP_IS_ZERO),
                 (fpIsNormal, Kind.FP_IS_NORMAL), (fpIsSubnormal, Kind.FP_IS_SUBNORMAL),
                 (fpIsNegative, Kind.FP_IS_NEG), (fpIsPositive, Kind.FP_IS_POS)):
        assert f(a).kind() == k
    # values fold
    assert float(simplify(FPVal(1.5, Float32()) + 1.0)) == 2.5
    assert float(simplify(fpSqrt(RNE(), FPVal(4.0, Float64())))) == 2.0
    assert bool(simplify(fpIsNaN(fpNaN(Float32())))) and bool(simplify(fpEQ(FPVal(1.0, Float32()), 1)))
    assert not bool(simplify(fpEQ(fpNaN(Float32()), fpNaN(Float32()))))  # IEEE: NaN != NaN
    assert bool(simplify(fpNaN(Float32()) == fpNaN(Float32())))  # SMT '=': the same value
    assert float(simplify(fpRoundToIntegral(RTZ(), FPVal(2.7, Float64())))) == 2.0
    s = Solver()
    mn = FP("mn", Float32())
    s.add(mn == fpMin(FPVal(1.0, Float32()), 2.0))  # fp.min over values is not folded either
    assert s.check() == sat and float(s.model()[mn]) == 1.0
    s.close()


def test_fp_conversions():
    a = FP("a", Float32())
    x = BitVec("x", 32)
    r = Real("r")
    t = fpToFP(RNE(), a, Float64())
    assert t.kind() == Kind.FP_TO_FP_FROM_FP and t.indices() == [11, 53] and t.sort() == Float64()
    assert fpFPToFP(RNE(), a, Float64()).kind() == Kind.FP_TO_FP_FROM_FP
    assert fpToFP(RNE(), x, Float32()).kind() == Kind.FP_TO_FP_FROM_SBV
    assert fpSignedToFP(RNE(), x, Float32()).kind() == Kind.FP_TO_FP_FROM_SBV
    assert fpUnsignedToFP(RNE(), x, Float32()).kind() == Kind.FP_TO_FP_FROM_UBV
    assert fpBVToFP(x, Float32()).kind() == Kind.FP_TO_FP_FROM_BV and fpBVToFP(BitVecVal(0x3F800000, 32), Float32()) is FPVal(1.0, Float32())
    assert float(fpToFP(RNE(), Q(1, 4), Float32())) == 0.25 and float(fpRealToFP(RNE(), Q(1, 2), Float64())) == 0.5
    with pytest.raises(Unsupported):
        fpToFP(RNE(), r, Float32())  # a Real must be a value in 3.0
    assert fpToSBV(RTZ(), a, 8).size() == 8 and fpToUBV(RTZ(), a, BitVecSort(16)).size() == 16
    assert fpToSBV(RTZ(), a, 8).kind() == Kind.FP_TO_SBV and fpToUBV(RTZ(), a, 8).kind() == Kind.FP_TO_UBV
    # the rewriter does not fold fp.to_sbv/fp.to_ubv over values: evaluate through a model
    s = Solver()
    sb, ub = BitVecs("sb ub", 8)
    s.add(sb == fpToSBV(RTZ(), FPVal(-2.5, Float32()), 8), ub == fpToUBV(RTZ(), FPVal(2.5, Float32()), 8))
    assert s.check() == sat and s.model()[sb].as_signed_long() == -2 and s.model()[ub].as_long() == 2
    s.close()
    assert fpToIEEEBV(a).size() == 32 and simplify(fpToIEEEBV(FPVal(1.0, Float32()))).as_long() == 0x3F800000
    assert fpToReal(a).kind() == Kind.FP_TO_REAL and fpToReal(a).children()[0] is a  # a symbolic float converts
    assert fpToReal(a).sexpr() == "(fp.to_real a)"
    assert fpToReal(FPVal(1.5, Float32())).as_fraction() == Fraction(3, 2)  # a value converts exactly
    assert fpToReal(FPVal(-0.0, Float32())).as_fraction() == 0
    assert fpToReal(fpNaN(Float32())).kind() == Kind.FP_TO_REAL  # no specified value: stays a term
    with pytest.raises(TypeError):
        fpToFP(RNE(), Bool("p"), Float32())
    with pytest.raises(TypeError):
        fpToSBV(RTZ(), x, 8)


def test_real_operators():
    set_main_tm(TermManager(simplify=False))
    a, b = Reals("a b")
    assert (a + b).kind() == Kind.REAL_ADD and (a - b).kind() == Kind.REAL_SUB and (-a).kind() == Kind.REAL_NEG
    assert (2 * a).kind() == Kind.REAL_MUL and (a * Fraction(1, 3)).kind() == Kind.REAL_MUL
    assert (a / 2).kind() == Kind.REAL_DIV and (1 + a).kind() == Kind.REAL_ADD and (1 - a).kind() == Kind.REAL_SUB
    assert (a < b).kind() in (Kind.REAL_LT, Kind.REAL_GT) and (a <= b).kind() in (Kind.REAL_LE, Kind.REAL_GE)
    assert (a > 1).kind() in (Kind.REAL_GT, Kind.REAL_LT) and (a >= Fraction(1, 2)).kind() in (Kind.REAL_GE, Kind.REAL_LE)
    with pytest.raises(Unsupported):
        a * b  # linear arithmetic only
    with pytest.raises(Unsupported):
        a / b
    assert simplify(Q(1, 3) + Q(1, 6)).as_fraction() == Fraction(1, 2)
    assert simplify(RealVal(3) * Q(1, 3)).as_fraction() == 1
    assert bool(Q(1, 3) < Q(1, 2)) and not bool(Q(1, 3) >= Q(1, 2)) and bool(Q(1, 2) == Fraction(1, 2))


def test_arrays():
    A = ArraySort(BitVecSort(32), BitVecSort(8))
    a = Array("a", BitVecSort(32), BitVecSort(8))
    assert a[5].kind() == Kind.SELECT and Select(a, BitVecVal(5, 32)).kind() == Kind.SELECT and a[5] is Select(a, 5)
    st = Store(a, 5, 42)
    assert st.kind() == Kind.STORE and st.sort() is A and Update is Store
    assert simplify(st[5]).as_long() == 42
    k = K(A, 0)
    assert k.kind() == Kind.CONST_ARRAY and k.sort() is A and Default(k).as_long() == 0
    assert K(BitVecSort(32), BitVecVal(9, 8)).sort() is A and simplify(K(A, 7)[3]).as_long() == 7
    assert simplify(Store(K(A, 0), 5, 0x2A)[5]).as_long() == 0x2A and simplify(Store(K(A, 0), 5, 0x2A)[6]).as_long() == 0
    fb = ArrayFromBytes(b"\x01\x02\x03")
    assert fb.sort() is A and simplify(fb[2]).as_long() == 3 and simplify(fb[7]).as_long() == 0
    assert ArrayFromBytes(b"\x01", 16).domain() == BitVecSort(16)
    eq = a == Store(K(A, 0), 5, 0x2A)  # equality over a constant array
    assert is_bool(eq) and eq.kind() == Kind.EQUAL
    with pytest.raises(TypeError):
        Select(BitVec("x", 8), 1)
    with pytest.raises(SortMismatch):
        Store(a, 5, BitVecVal(1, 16))
    with pytest.raises(ArgumentError):
        a[1 << 40]


def test_functions():
    B8 = BitVecSort(8)
    f = Function("f", B8, B8)
    g = Function("g", B8, B8, BoolSort())
    x, y = BitVecs("x y", 8)
    assert f(x).kind() == Kind.APPLY and f(x).sort() is B8 and f(x).num_args() == 2 and f(x).arg(0) is f
    assert f(3).arg(1).as_long() == 3 and g(x, y).sort() == BoolSort()
    with pytest.raises(ArgumentError) as e:
        f(1, 2)
    assert e.value.code == ErrorCode.ARITY
    with pytest.raises(SortMismatch):
        f(BitVec("w", 16))
    with pytest.raises(TypeError):
        f(1.5)
    assert is_func_decl(f) and not is_func_decl(x)


def test_uninterpreted_sorts():
    S = DeclareSort("S")
    p, q = Consts("p q", S)
    assert (p == q).kind() == Kind.EQUAL and Distinct(p, q).kind() == Kind.DISTINCT
    f = Function("h", S, BitVecSort(8))
    assert f(p).sort() == BitVecSort(8)
    with pytest.raises(TypeError):
        p == 1


# ---------------------------------------------------------------- introspection and printing


def test_introspection_and_printing():
    x, y = BitVecs("x y", 8)
    t = x + 3 * y
    assert t.kind() == Kind.BV_ADD and t.kind().smtlib == "bvadd" and Kind.BV_EXTRACT.smtlib == "(_ extract hi lo)"
    assert t.num_args() == 2 and len(t.children()) == 2 and t.arg(-1) is t.children()[-1] and t.indices() == []
    with pytest.raises(IndexError):
        t.arg(2)
    assert repr(t) in ("(bvadd x (bvmul #x03 y))", "(bvadd (bvmul #x03 y) x)")
    assert t.sexpr() == repr(t) and "  " not in repr(t)
    # the text is the printer's own: a quoted name keeps its spaces
    odd = BitVec("odd  name", 8)
    assert repr(odd) == "|odd  name|" and repr(odd + 1) in ("(bvadd |odd  name| #x01)", "(bvadd #x01 |odd  name|)")
    assert str(t) in ("x + (3 * y)", "(3 * y) + x")
    assert str(x == 7) == "x == 7" and str(If(Bool("p"), x, y)) == "If(p, x, y)"
    assert str(Extract(3, 0, x)) == "Extract(3, 0, x)" and str(ULT(x, y)) in ("ULT(x, y)", "UGT(y, x)")
    assert str(And(Bool("p"), Bool("q"))) == "And(p, q)" and str(Not(Bool("p"))) == "Not(p)"
    a = Array("arr", BitVecSort(32), BitVecSort(8))
    assert str(a[5]) == "arr[5]" and str(Store(a, 5, 1)) == "Store(arr, 5, 1)"
    f = Function("f", BitVecSort(8), BitVecSort(8))
    assert str(f(x)) == "f(x)"
    fa = FP("fa", Float32())
    assert str(fa + 1.5) == "fa + 1.5" and str(fpAdd(RTZ(), fa, 1.5)) == "fpAdd(RTZ, fa, 1.5)"
    assert str(Q(1, 3)) == "1/3" and str(RealVal(2)) == "2" and str(BoolVal(True)) == "True" and str(RNE()) == "RNE"
    assert str(fpNaN(Float32())) == "NaN" and str(fpMinusZero(Float32())) == "-0.0" and str(fpPlusInfinity(Float32())) == "+oo"
    assert t.to_string("smtlib2") == t.sexpr()
    assert "bvadd" in t.to_string("smtlib2")
    cvc = t.to_string("cvc")
    assert "BVPLUS" in cvc or "+" in cvc
    assert t.to_string("dot").startswith("digraph") or "->" in t.to_string("dot")
    with pytest.raises(ArgumentError):
        t.to_string("pdf")
    assert x.decl_name() == "x" and (x + y).decl_name() is None
    assert is_expr(x) and is_app(t) and is_const(x) and is_const(BitVecVal(1, 8)) and not is_const(t)
    assert is_symbol(x) and not is_symbol(BitVecVal(1, 8)) and is_value(BitVecVal(1, 8)) and not is_value(x)
    assert is_bv(x) and is_bv_value(BitVecVal(1, 8)) and not is_bv_value(x) and is_bool(Bool("p"))
    assert is_fp(fa) and is_fp_value(FPVal(1.0, Float32())) and is_real(Real("r")) and is_rational_value(Q(1, 2))
    assert is_array(a) and not is_expr(3) and not is_app(3)
    s = t.substitute((x, BitVecVal(1, 8)), (y, BitVecVal(2, 8)))
    assert simplify(s).as_long() == 7 and substitute(t, (x, 1)).kind() in (Kind.BV_ADD, Kind.VALUE)
    with pytest.raises(TypeError):
        t.substitute((1, x))


def test_pickle_and_translate():
    x, y = BitVecs("x y", 8)
    t = x + 3 * y
    t2 = pickle.loads(pickle.dumps(t))
    assert t2 is t  # rebuilt through the default manager's name table
    tm2 = TermManager(simplify=False)
    t3 = t.translate(tm2)
    assert t3.manager() is tm2 and t3.sexpr() == t.sexpr() and t3.translate(main_tm()) is t and t.translate(main_tm()) is t
    with pytest.raises(SortMismatch):
        t3 + x
    A = ArraySort(BitVecSort(32), BitVecSort(8))
    f = Function("f", BitVecSort(8), BitVecSort(8))
    S = DeclareSort("S")
    p = Const("p", S)
    for term in (fpAdd(RTZ(), FP("fa", Float32()), 1.5), K(A, 7), Store(Array("a", BitVecSort(32), BitVecSort(8)), 1, 2),
                 f(x), Extract(3, 0, x), fpToFP(RNE(), x, Float32()), Q(1, 3) + Real("r"), p == Const("q", S),
                 BitVecVal(-(1 << 100), 128), Bool("b") & Bool("c")):
        back = pickle.loads(pickle.dumps(term))
        assert back is term, term
        assert term.translate(tm2).sexpr() == term.sexpr()
    with pytest.raises(Unsupported):
        pickle.dumps(FreshConst(BitVecSort(8)) + 1)  # anonymous symbols cannot be rebuilt by name


def test_copies_are_the_values_themselves():
    """Terms, sorts and models are immutable values of their manager: copy and deepcopy give
    the object itself, where the pickling path would have moved it to the default manager."""
    import copy
    tm = TermManager()
    x = BitVec("x", 8, tm=tm)
    fresh = FreshConst(BitVecSort(8, tm=tm))
    for v in (x, x + 1, fresh, x.sort(), BitVecSort(8, tm=tm)):
        assert copy.copy(v) is v and copy.deepcopy(v) is v
    assert copy.deepcopy([x, fresh])[1] is fresh
    assert (x + copy.copy(x)).manager() is tm
    s = Solver(tm=tm)
    s.add(x == 3)
    assert s.check() == sat
    m = s.model()
    assert copy.copy(m) is m and copy.deepcopy(m) is m
    s.close()


def test_all_exports_exist():
    for name in stp.__all__:
        assert hasattr(stp, name), name


def test_deep_terms_print_pickle_translate_and_decide():
    # 20 000 levels: far past Python's recursion limit, which str(), pickling, translate()
    # and bool() each reached walking a term one call per level
    x = BitVec("x", 32)
    t = x
    for _ in range(10000):
        t = t * 3 + 1
    text = str(t)
    assert text.count("*") == 10000 and text.count("+") == 10000
    assert pickle.loads(pickle.dumps(t)) is t
    tm2 = TermManager()
    assert t.translate(tm2).sexpr() == t.sexpr()
    assert bool(Not(t == t + 0)) is False
