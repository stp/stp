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

"""str(term): the infix, z3py-flavoured rendering (untruncated). repr(term) is SMT-LIB 2."""

from fractions import Fraction

from . import _core
from ._gen_kinds import Kind

_INFIX = {
    Kind.EQUAL: "==",
    Kind.BV_ADD: "+", Kind.BV_SUB: "-", Kind.BV_MUL: "*",
    Kind.BV_AND: "&", Kind.BV_OR: "|", Kind.BV_XOR: "^",
    Kind.BV_SHL: "<<", Kind.BV_ASHR: ">>",
    Kind.BV_SLT: "<", Kind.BV_SLE: "<=", Kind.BV_SGT: ">", Kind.BV_SGE: ">=",
    Kind.REAL_ADD: "+", Kind.REAL_SUB: "-", Kind.REAL_MUL: "*", Kind.REAL_DIV: "/",
    Kind.REAL_LT: "<", Kind.REAL_LE: "<=", Kind.REAL_GT: ">", Kind.REAL_GE: ">=",
    Kind.FP_LT: "<", Kind.FP_LEQ: "<=", Kind.FP_GT: ">", Kind.FP_GEQ: ">=",
}

_FP_INFIX = {Kind.FP_ADD: "+", Kind.FP_SUB: "-", Kind.FP_MUL: "*", Kind.FP_DIV: "/"}

_PREFIX = {
    Kind.NOT: "Not", Kind.AND: "And", Kind.OR: "Or", Kind.XOR: "Xor", Kind.IMPLIES: "Implies",
    Kind.ITE: "If", Kind.DISTINCT: "Distinct",
    Kind.BV_NAND: "BVNand", Kind.BV_NOR: "BVNor", Kind.BV_XNOR: "BVXnor",
    Kind.BV_UDIV: "UDiv", Kind.BV_UREM: "URem", Kind.BV_SDIV: "SDiv", Kind.BV_SREM: "SRem", Kind.BV_SMOD: "SMod",
    Kind.BV_LSHR: "LShR", Kind.BV_CONCAT: "Concat", Kind.BV_COMP: "BVComp",
    Kind.BV_ULT: "ULT", Kind.BV_ULE: "ULE", Kind.BV_UGT: "UGT", Kind.BV_UGE: "UGE",
    Kind.BV_UADDO: "bvuaddo", Kind.BV_SADDO: "bvsaddo", Kind.BV_UMULO: "bvumulo", Kind.BV_SMULO: "bvsmulo",
    Kind.BV_USUBO: "bvusubo", Kind.BV_SSUBO: "bvssubo", Kind.BV_NEGO: "bvnego", Kind.BV_SDIVO: "bvsdivo",
    Kind.BV_REDAND: "BVRedAnd", Kind.BV_REDOR: "BVRedOr",
    Kind.STORE: "Store",
    Kind.FP_ABS: "fpAbs", Kind.FP_NEG: "fpNeg", Kind.FP_ADD: "fpAdd", Kind.FP_SUB: "fpSub", Kind.FP_MUL: "fpMul",
    Kind.FP_DIV: "fpDiv", Kind.FP_FMA: "fpFMA", Kind.FP_SQRT: "fpSqrt", Kind.FP_REM: "fpRem",
    Kind.FP_RTI: "fpRoundToIntegral", Kind.FP_MIN: "fpMin", Kind.FP_MAX: "fpMax",
    Kind.FP_EQ: "fpEQ", Kind.FP_IS_NORMAL: "fpIsNormal", Kind.FP_IS_SUBNORMAL: "fpIsSubnormal",
    Kind.FP_IS_ZERO: "fpIsZero", Kind.FP_IS_INF: "fpIsInf", Kind.FP_IS_NAN: "fpIsNaN",
    Kind.FP_IS_NEG: "fpIsNegative", Kind.FP_IS_POS: "fpIsPositive", Kind.FP_FP: "fpFP",
    Kind.FP_TO_REAL: "fpToReal", Kind.FP_TO_IEEE_BV: "fpToIEEEBV",
}

_INDEXED = {
    Kind.BV_EXTRACT: "Extract", Kind.BV_ZERO_EXTEND: "ZeroExt", Kind.BV_SIGN_EXTEND: "SignExt",
    Kind.BV_REPEAT: "RepeatBitVec", Kind.BV_ROTATE_LEFT: "RotateLeft", Kind.BV_ROTATE_RIGHT: "RotateRight",
}

_TO_FP = {
    Kind.FP_TO_FP_FROM_BV: "fpBVToFP", Kind.FP_TO_FP_FROM_FP: "fpToFP", Kind.FP_TO_FP_FROM_SBV: "fpSignedToFP",
    Kind.FP_TO_FP_FROM_UBV: "fpUnsignedToFP", Kind.FP_TO_FP_FROM_REAL: "fpRealToFP",
    Kind.FP_TO_UBV: "fpToUBV", Kind.FP_TO_SBV: "fpToSBV",
}


def _value(t):
    k = t.sort_kind()
    if k == _core.SORT_BOOL:
        return "True" if t.to_bool() else "False"
    if k == _core.SORT_BV:
        return str(t.to_uint())
    if k == _core.SORT_FP:
        exp_size, sig_size, sign, biased, cls, sig = t.to_fp()
        if cls == _core.FP_NAN:
            return "NaN"
        if cls == _core.FP_INFINITY:
            return "-oo" if sign else "+oo"
        if cls == _core.FP_ZERO:
            return "-0.0" if sign else "0.0"
        if exp_size <= 11 and sig_size <= 53:
            return repr(t.fp_to_double())
        return t.sexpr()
    if k == _core.SORT_RM:
        return _core.rm_name(t.to_rm())
    if k == _core.SORT_REAL:
        num, den = t.real_numerator(), t.real_denominator()
        return num if den == "1" else "%s/%s" % (num, den)
    return t.sexpr()


def _atom(s):
    return s if s and s[0] not in "(" and " " not in s or s.startswith(("(", "[")) and _balanced(s) else "(" + s + ")"


def _balanced(s):
    # a single bracketed group, e.g. "f(x, y)" or "a[i]" -> True, "a + b" -> False
    depth = 0
    for i, ch in enumerate(s):
        if ch in "([":
            depth += 1
        elif ch in ")]":
            depth -= 1
            if depth == 0 and i != len(s) - 1:
                return False
        elif depth == 0 and ch == " ":
            return False
    return True


def _paren(s):
    return s if _balanced(s) else "(" + s + ")"


def pretty(t):
    if t.is_value():
        return _value(t)
    kind = Kind(t.kind())
    if kind == Kind.CONSTANT:
        return t.symbol() or t.sexpr()
    children = t.children()
    if kind in _INFIX and len(children) == 2:
        return "%s %s %s" % (_paren(pretty(children[0])), _INFIX[kind], _paren(pretty(children[1])))
    if kind in _FP_INFIX and len(children) == 3:
        rm = children[0]
        if rm.is_value() and rm.to_rm() == t._manager().default_rounding_mode:
            return "%s %s %s" % (_paren(pretty(children[1])), _FP_INFIX[kind], _paren(pretty(children[2])))
    if kind == Kind.DISTINCT and len(children) == 2:
        return "%s != %s" % (_paren(pretty(children[0])), _paren(pretty(children[1])))
    if kind == Kind.BV_NEG or kind == Kind.REAL_NEG:
        return "-" + _paren(pretty(children[0]))
    if kind == Kind.BV_NOT:
        return "~" + _paren(pretty(children[0]))
    if kind == Kind.SELECT:
        return "%s[%s]" % (_paren(pretty(children[0])), pretty(children[1]))
    if kind == Kind.APPLY:
        return "%s(%s)" % (pretty(children[0]), ", ".join(pretty(c) for c in children[1:]))
    if kind == Kind.CONST_ARRAY:
        return "K(%r, %s)" % (t.sort(), pretty(children[0]))
    if kind in _INDEXED:
        idx = t.indices()
        if kind == Kind.BV_EXTRACT:
            return "Extract(%d, %d, %s)" % (idx[0], idx[1], pretty(children[0]))
        if kind in (Kind.BV_ROTATE_LEFT, Kind.BV_ROTATE_RIGHT):
            return "%s(%s, %d)" % (_INDEXED[kind], pretty(children[0]), idx[0])
        return "%s(%d, %s)" % (_INDEXED[kind], idx[0], pretty(children[0]))
    if kind in _TO_FP:
        idx = t.indices()
        args = ", ".join(pretty(c) for c in children)
        if kind in (Kind.FP_TO_UBV, Kind.FP_TO_SBV):
            return "%s(%s, %d)" % (_TO_FP[kind], args, idx[0])
        return "%s(%s, FPSort(%d, %d))" % (_TO_FP[kind], args, idx[0], idx[1])
    name = _PREFIX.get(kind) or Kind(kind).name
    return "%s(%s)" % (name, ", ".join(pretty(c) for c in children))
