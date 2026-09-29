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

"""The term layer of the STP 3.x Python API: the term manager, sorts, the ExprRef
family with its operators and literal coercion, and the z3py-style builders.
Everything here is pure Python over stp._core."""

import enum
import threading
from fractions import Fraction

from . import _core
from ._core import (Error, ArgumentError, SortMismatch, DoesNotFit, NotAValue, NoModel, Unsupported,
                    OptionError, UnknownOption, ParseError, IOError, StateError, ResourceError, InternalError)
from ._gen_kinds import Kind, ErrorCode, Option, SMTLIB_NAMES

# ---------------------------------------------------------------- enums


class SortKind(enum.IntEnum):
    BOOL = _core.SORT_BOOL
    BV = _core.SORT_BV
    FP = _core.SORT_FP
    RM = _core.SORT_RM
    REAL = _core.SORT_REAL
    ARRAY = _core.SORT_ARRAY
    FUN = _core.SORT_FUN
    UNINTERPRETED = _core.SORT_UNINTERPRETED


class RoundingMode(enum.IntEnum):
    RNE = _core.RM_RNE
    RNA = _core.RM_RNA
    RTP = _core.RM_RTP
    RTN = _core.RM_RTN
    RTZ = _core.RM_RTZ


class UnknownReason(str, enum.Enum):
    """A string enum: compares equal to its lower-case name ("timeout")."""
    NONE = "none"
    TIMEOUT = "timeout"
    CONFLICT_LIMIT = "conflict-limit"
    INTERRUPTED = "interrupted"
    INCOMPLETE = "incomplete"
    RESOURCE_LIMIT = "resource-limit"
    CARRIER_EXHAUSTED = "carrier-exhausted"
    ASSUMED_INJECTIVITY = "assumed-injectivity"
    STOPPED_AFTER_CNF = "stopped-after-cnf"
    OTHER = "other"

    def __str__(self):
        return self.value

    def __hash__(self):
        return hash(self.value)

    def __eq__(self, other):
        if isinstance(other, str):
            return self.value == str(other)
        return NotImplemented

    def __ne__(self, other):
        r = self.__eq__(other)
        return r if r is NotImplemented else not r


_UNKNOWN_REASONS = list(UnknownReason)  # by C value: NONE = 0 ... OTHER = 9


def _reason(code):
    return _UNKNOWN_REASONS[code] if 0 <= code < len(_UNKNOWN_REASONS) else UnknownReason.OTHER


class Tier(enum.IntEnum):
    STABLE = _core.TIER_STABLE
    EXPERT = _core.TIER_EXPERT
    EXPERIMENTAL = _core.TIER_EXPERIMENTAL
    DIAGNOSTIC = _core.TIER_DIAGNOSTIC


def _add_smtlib_property():
    # Kind.smtlib: the SMT-LIB 2 spelling of the kind (from the generated table)
    def smtlib(self):
        return SMTLIB_NAMES.get(self, "?")
    Kind.smtlib = property(smtlib)


_add_smtlib_property()

_FORMATS = {
    "auto": _core.FORMAT_AUTO,
    "smtlib2": _core.FORMAT_SMTLIB2,
    "smt2": _core.FORMAT_SMTLIB2,
    "dot": _core.FORMAT_DOT,
    "gdl": _core.FORMAT_GDL,
}


def _format_code(name):
    try:
        return _FORMATS[str(name).lower()]
    except KeyError:
        raise ArgumentError("unknown format %r; expected one of %s" % (name, ", ".join(sorted(_FORMATS))),
                            code=ErrorCode.INVALID_ARGUMENT) from None


# ---------------------------------------------------------------- the term manager


class TermManager(_core.Manager):
    """A term manager: the node factory, the sort pool and the one name table.

    TermManager(simplify=True, default_rounding_mode=RoundingMode.RNE, options=None,
    uf_sort_width=16). `options` supplies the manager-scoped entries (simplify,
    default-rounding-mode, uf-sort-width) by name, in any form Solver takes (an Options
    object, a solver's live options, a dict); the keyword arguments override it."""

    def __init__(self, simplify=None, default_rounding_mode=None, options=None, uf_sort_width=None):
        if options is None and uf_sort_width is None:
            super().__init__(None, True if simplify is None else bool(simplify),
                             int(_rm_enum(default_rounding_mode)) if default_rounding_mode is not None else _core.RM_RNE,
                             16)
            return
        from ._solver import Options
        if options is None:
            handle = _core.OptionsHandle()
        elif isinstance(options, Options):
            handle = options.copy()._handle  # a detached copy, of a live view too
        elif isinstance(options, _core.OptionsHandle):
            handle = options.copy()
        elif isinstance(options, dict):
            handle = _core.OptionsHandle()
            Options._wrap(handle).set(options)
        else:
            raise TypeError("options must be an Options object or a dict, got %s" % type(options).__name__)
        if simplify is not None:
            handle.set_bool("simplify", bool(simplify))
        if default_rounding_mode is not None:
            handle.set_str("default-rounding-mode", _rm_enum(default_rounding_mode).name)
        if uf_sort_width is not None:
            Options._wrap(handle).set("uf-sort-width", uf_sort_width)
        super().__init__(handle)

    @property
    def default_rounding_mode(self):
        """The mode FP operators use when none is given (read/write)."""
        return RoundingMode(_core.Manager.default_rounding_mode.__get__(self))

    @default_rounding_mode.setter
    def default_rounding_mode(self, rm):
        _core.Manager.default_rounding_mode.__set__(self, int(_rm_enum(rm)))

    def mk_term(self, kind, args, indices=(), sort=None):
        """The generic constructor: kind, the argument terms, the integer indices in SMT-LIB
        order and, for CONST_ARRAY, the result sort."""
        return _core.Manager.mk_term(self, int(kind), list(args), tuple(int(i) for i in indices), sort)

    def mk_fresh(self, sort, prefix=""):
        return _core.Manager.mk_fresh(self, sort, prefix)

    def __repr__(self):
        return "TermManager(id=%d)" % self.id


_main_lock = threading.Lock()
_main = None


def main_tm():
    """The lazily created default manager (process-wide; creation is locked)."""
    global _main
    if _main is None:
        with _main_lock:
            if _main is None:
                _main = TermManager()
    return _main


def set_main_tm(tm):
    """Replace the default manager."""
    global _main
    if not isinstance(tm, TermManager):
        raise TypeError("set_main_tm expects a TermManager")
    with _main_lock:
        _main = tm


def _tm(tm=None, ctx=None):
    if tm is not None and ctx is not None and tm is not ctx:
        raise ArgumentError("tm= and ctx= name different managers", code=ErrorCode.INVALID_ARGUMENT)
    if tm is None:
        tm = ctx
    if tm is None:
        return main_tm()
    if not isinstance(tm, TermManager):
        raise TypeError("tm must be a TermManager, got %s" % type(tm).__name__)
    return tm


def _rm_enum(rm):
    if isinstance(rm, RoundingMode):
        return rm
    if isinstance(rm, str):
        try:
            return RoundingMode[rm.upper()]
        except KeyError:
            raise ArgumentError("unknown rounding mode %r" % (rm,), code=ErrorCode.INVALID_ARGUMENT) from None
    if isinstance(rm, int) and not isinstance(rm, bool):
        return RoundingMode(rm)
    raise TypeError("a rounding mode is a RoundingMode member, got %s" % type(rm).__name__)


# ---------------------------------------------------------------- sorts


class SortRef(_core.Sort):
    """A sort. Sorts compare structurally with bool (they are not terms) and are pooled by
    their manager, so equal sorts are the same object."""

    def kind(self):
        return SortKind(_core.Sort.kind(self))

    def name(self):
        k = self.kind()
        if k == SortKind.UNINTERPRETED:
            return self.uninterpreted_name()
        return {SortKind.BOOL: "Bool", SortKind.BV: "BitVec", SortKind.FP: "FloatingPoint",
                SortKind.RM: "RoundingMode", SortKind.REAL: "Real", SortKind.ARRAY: "Array",
                SortKind.FUN: "Function"}[k]

    def manager(self):
        return self._manager()

    def __eq__(self, other):
        if not isinstance(other, SortRef):
            return NotImplemented
        return self.same(other)

    def __ne__(self, other):
        if not isinstance(other, SortRef):
            return NotImplemented
        return not self.same(other)

    def __hash__(self):
        return hash((self._manager().id, self.id))

    def __repr__(self):
        return self.name()

    def __str__(self):
        return self.__repr__()

    def sexpr(self):
        return _core.Sort.sexpr(self)

    def __reduce__(self):
        from . import _smt2
        return (_smt2.unpickle_sort, (_smt2.sort_text(self),))

    # A sort is an immutable value of its manager: a copy is the sort itself
    # (pickling, above, is what moves one to another manager).
    def __copy__(self):
        return self

    def __deepcopy__(self, memo):
        return self

    def translate(self, tm):
        from . import _smt2
        return _smt2.translate_sort(self, tm)

    # the Python default of this sort (what model completion would give)
    def _default_value(self):
        k = self.kind()
        tm = self._manager()
        if k == SortKind.BOOL:
            return tm.mk_bool(False)
        if k == SortKind.BV:
            return tm.mk_bv(self.size(), 0)
        if k == SortKind.FP:
            return tm.mk_fp_special(self, "+zero")
        if k == SortKind.RM:
            return tm.mk_rm(_core.RM_RNE)
        if k == SortKind.REAL:
            return tm.mk_real_str("0")
        if k == SortKind.ARRAY:
            return tm.mk_const_array(self, self.range()._default_value())
        raise Unsupported("no default value for a %s sort" % self.name(), code=ErrorCode.UNSUPPORTED)


class BoolSortRef(SortRef):
    def __repr__(self):
        return "BoolSort()"


class BitVecSortRef(SortRef):
    def size(self):
        return self.bv_size()

    def __repr__(self):
        return "BitVecSort(%d)" % self.size()


class FPSortRef(SortRef):
    def ebits(self):
        return self.fp_ebits()

    def sbits(self):
        return self.fp_sbits()

    def __repr__(self):
        return "FPSort(%d, %d)" % (self.ebits(), self.sbits())


class RMSortRef(SortRef):
    def __repr__(self):
        return "RoundingModeSort()"


class RealSortRef(SortRef):
    def __repr__(self):
        return "RealSort()"


class ArraySortRef(SortRef):
    def domain(self):
        return self.array_index()

    def range(self):
        return self.array_element()

    def __repr__(self):
        return "ArraySort(%r, %r)" % (self.domain(), self.range())


class FuncSortRef(SortRef):
    def arity(self):
        return self.fun_arity()

    def domain(self, i):
        n = self.arity()
        if not isinstance(i, int) or i < 0 or i >= n:
            raise IndexError("domain index %r out of range for a function of arity %d" % (i, n))
        return self.fun_domain(i)

    def domains(self):
        return [self.fun_domain(i) for i in range(self.arity())]

    def range(self):
        return self.fun_codomain()

    def __repr__(self):
        return "FuncSort(%s)" % ", ".join(repr(s) for s in self.domains() + [self.range()])


class UninterpretedSortRef(SortRef):
    def __repr__(self):
        return "DeclareSort(%r)" % self.name()


_core.register_sort_classes({
    SortKind.BOOL: BoolSortRef,
    SortKind.BV: BitVecSortRef,
    SortKind.FP: FPSortRef,
    SortKind.RM: RMSortRef,
    SortKind.REAL: RealSortRef,
    SortKind.ARRAY: ArraySortRef,
    SortKind.FUN: FuncSortRef,
    SortKind.UNINTERPRETED: UninterpretedSortRef,
})


def BoolSort(tm=None, ctx=None):
    return _tm(tm, ctx).bool_sort()


def BitVecSort(n, tm=None, ctx=None):
    return _tm(tm, ctx).bv_sort(n)


def FPSort(ebits, sbits, tm=None, ctx=None):
    return _tm(tm, ctx).fp_sort(ebits, sbits)


def Float16(tm=None, ctx=None):
    return _tm(tm, ctx).fp_sort(5, 11)


def Float32(tm=None, ctx=None):
    return _tm(tm, ctx).fp_sort(8, 24)


def Float64(tm=None, ctx=None):
    return _tm(tm, ctx).fp_sort(11, 53)


def Float128(tm=None, ctx=None):
    return _tm(tm, ctx).fp_sort(15, 113)


FloatHalf = Float16
FloatSingle = Float32
FloatDouble = Float64
FloatQuadruple = Float128


def RoundingModeSort(tm=None, ctx=None):
    return _tm(tm, ctx).rm_sort()


def RealSort(tm=None, ctx=None):
    return _tm(tm, ctx).real_sort()


def ArraySort(index, element):
    _check_sort(index, "ArraySort")
    _check_sort(element, "ArraySort")
    return index.manager().array_sort(index, element)


def FuncSort(*domain_then_range):
    if len(domain_then_range) < 1:
        raise ArgumentError("FuncSort needs at least the range sort", code=ErrorCode.INVALID_ARGUMENT)
    for s in domain_then_range:
        _check_sort(s, "FuncSort")
    rng = domain_then_range[-1]
    return rng.manager().fun_sort(list(domain_then_range[:-1]), rng)


def DeclareSort(name, tm=None, ctx=None):
    return _tm(tm, ctx).declare_sort(name)


def FreshSort(prefix="S", tm=None, ctx=None):
    return _tm(tm, ctx).mk_fresh_sort(prefix)


def _check_sort(s, where):
    if not isinstance(s, SortRef):
        raise TypeError("%s: expected a sort, got %s" % (where, type(s).__name__))


# ---------------------------------------------------------------- literal coercion


class _NoCoercion(Exception):
    """The operand is neither a term nor a literal of this sort's shape."""


def _is_int(v):
    return isinstance(v, int) and not isinstance(v, bool)


def _coerce(sort, v, rm=None):
    """A term of `sort` for the Python literal v (or v itself when it is a term).
    Raises TypeError for a number that cannot take this sort, _NoCoercion for a foreign object."""
    if isinstance(v, ExprRef):
        return v
    tm = sort.manager()
    k = sort.kind()
    if k == SortKind.BOOL:
        if isinstance(v, bool):
            return tm.mk_bool(v)
        if isinstance(v, (int, float, Fraction)):
            raise TypeError("cannot coerce %r to Bool (use BoolVal)" % (v,))
        raise _NoCoercion()
    if k == SortKind.BV:
        if isinstance(v, bool) or _is_int(v):
            return tm.mk_bv(sort.size(), int(v))  # strict: VALUE_OUT_OF_RANGE from the C layer
        if isinstance(v, (float, Fraction)):
            raise TypeError("cannot coerce %r to %r: a bit-vector literal is an int" % (v, sort))
        raise _NoCoercion()
    if k == SortKind.FP:
        mode = int(_rm_enum(rm)) if rm is not None else int(tm.default_rounding_mode)
        if isinstance(v, bool):
            raise TypeError("cannot coerce %r to %r" % (v, sort))
        if isinstance(v, float):
            return tm.mk_fp_double(sort, mode, v)
        if isinstance(v, int):
            return tm.mk_fp_decimal(sort, mode, str(v))
        if isinstance(v, Fraction):
            return tm.mk_fp_decimal(sort, mode, "%d/%d" % (v.numerator, v.denominator))
        if isinstance(v, str):
            return tm.mk_fp_decimal(sort, mode, v)
        raise _NoCoercion()
    if k == SortKind.RM:
        if isinstance(v, RoundingMode):
            return tm.mk_rm(int(v))
        if isinstance(v, (int, float, Fraction)):
            raise TypeError("cannot coerce %r to RoundingMode (use RNE(), RTZ(), ...)" % (v,))
        raise _NoCoercion()
    if k == SortKind.REAL:
        if isinstance(v, bool):
            raise TypeError("cannot coerce %r to Real" % (v,))
        if isinstance(v, int):
            return tm.mk_real_str(str(v))
        if isinstance(v, Fraction):
            return tm.mk_real_str("%d/%d" % (v.numerator, v.denominator))
        if isinstance(v, float):
            raise TypeError("a Python float cannot take sort Real: use Fraction, RealVal('%r') or Q(p, q)" % (v,))
        if isinstance(v, str):
            return tm.mk_real_str(v)
        raise _NoCoercion()
    if isinstance(v, (bool, int, float, Fraction)):
        raise TypeError("cannot coerce %r to %r" % (v, sort))
    raise _NoCoercion()


def _coerce_arg(sort, v, rm=None):
    """_coerce, turning a foreign object into a TypeError (for named builders)."""
    try:
        return _coerce(sort, v, rm)
    except _NoCoercion:
        raise TypeError("expected a term of sort %r or a literal, got %s" % (sort, type(v).__name__)) from None


def _binop(kind, a, b, rm=None):
    """a op b with literal coercion on either side (a or b is a term); rm is the rounding-mode
    TERM of an FP operation (a literal operand is rounded under it when it is a value)."""
    mode = rm.as_rounding_mode() if isinstance(rm, RMNumRef) else None
    if isinstance(a, ExprRef):
        b = _coerce(a.sort(), b, mode)
        tm = a._manager()
    else:
        a = _coerce(b.sort(), a, mode)
        tm = b._manager()
    if rm is not None:
        return tm.mk_term(kind, [rm, a, b])
    return tm.mk_term(kind, [a, b])


def _term_of(args, where):
    """The first term among args (to find the manager); TypeError if there is none."""
    for a in args:
        if isinstance(a, ExprRef):
            return a
    return None


def _mk(kind, args, indices=(), sort=None):
    t = _term_of(args, kind)
    tm = t._manager() if t is not None else main_tm()
    return tm.mk_term(kind, list(args), indices, sort)


# ---------------------------------------------------------------- terms


class ExprRef(_core.Term):
    """A term. `==` builds EQUAL (SMT '=') for every sort and `!=` builds DISTINCT.
    Operands: another term of this manager, or a Python literal coercible to this term's
    sort. `x == None` and objects that are neither terms nor numbers -> NotImplemented
    (Python answers False by identity); a number that cannot coerce to the sort ->
    TypeError naming the sort; a term of another manager -> SortMismatch."""

    def kind(self):
        return Kind(_core.Term.kind(self))

    def num_args(self):
        return self.num_children()

    def arg(self, i):
        return self.child(i)

    def manager(self):
        return self._manager()

    def is_symbol(self):
        return self.is_const()

    def decl_name(self):
        return self.symbol()

    def eq(self, other):
        """Structural equality: the same term (the explicit test; `==` builds a term)."""
        return isinstance(other, ExprRef) and self.same(other)

    def __eq__(self, other):
        if other is None:
            return NotImplemented
        try:
            return _binop(Kind.EQUAL, self, other)
        except _NoCoercion:
            return NotImplemented

    def __ne__(self, other):
        if other is None:
            return NotImplemented
        try:
            return _binop(Kind.DISTINCT, self, other)
        except _NoCoercion:
            return NotImplemented

    def __hash__(self):
        return hash((self._manager().id, self.id))

    def __bool__(self):
        # Only a GROUND Bool term has a truth value; fold first so that it never depends
        # on the manager's simplify setting. The engine's local rewriter leaves a few ground
        # shapes alone (distinct over values, Real relations over values); those are
        # decided here.
        if self.sort_kind() == SortKind.BOOL:
            t = self._manager().simplify_term(self)
            if t.is_value():
                return t.to_bool()
            v = _ground_truth(t)
            if v is not None:
                return v
        raise TypeError(
            "a term has no truth value (%s); use t.eq(u) or `is` for identity, and a Solver for satisfiability"
            % self.sexpr())

    def __repr__(self):
        return self.sexpr()

    def __str__(self):
        from . import _pretty
        return _pretty.pretty(self)

    def to_string(self, format="smtlib2"):
        code = _format_code(format)
        if code == _core.FORMAT_SMTLIB2:
            return self.sexpr()
        return _core.Term.to_string(self, code, False)

    def substitute(self, *pairs):
        if len(pairs) == 1 and isinstance(pairs[0], (list, tuple)) and pairs[0] and isinstance(pairs[0][0], (list, tuple)):
            pairs = tuple(pairs[0])
        froms = []
        tos = []
        for pair in pairs:
            if not (isinstance(pair, (tuple, list)) and len(pair) == 2):
                raise TypeError("substitute takes (from, to) pairs")
            a, b = pair
            if not isinstance(a, ExprRef):
                raise TypeError("substitute: the source of a pair must be a term")
            froms.append(a)
            tos.append(_coerce_arg(a.sort(), b))
        return self._manager().substitute(self, froms, tos)

    def translate(self, tm):
        from . import _smt2
        return _smt2.translate_term(self, tm)

    def __reduce__(self):
        from . import _smt2
        return _smt2.reduce_term(self)

    # A term is an immutable value of its manager: a copy is the term itself
    # (pickling, above, is what moves one to another manager).
    def __copy__(self):
        return self

    def __deepcopy__(self, memo):
        return self

    def __iter__(self):
        raise TypeError("terms are not iterable")

    def __contains__(self, item):
        raise TypeError("terms are not containers")

    # z3py compatibility
    def get_id(self):
        return self.id

    def sexpr(self):
        return _core.Term.sexpr(self)

    def ctx_ref(self):
        return self._manager()


def _ground_value(t):
    """The Python value of a ground term (bool, int for BV, Fraction for Real, the term itself
    for other value sorts), or None when a symbol remains."""
    if t.is_value():
        k = t.sort_kind()
        if k == SortKind.BOOL:
            return t.to_bool()
        if k == SortKind.BV:
            return t.to_uint()
        if k == SortKind.REAL:
            return Fraction(int(t.real_numerator()), int(t.real_denominator()))
        return t
    v = _ground_truth(t) if t.sort_kind() == SortKind.BOOL else None
    return v


def _ground_truth(t):
    """True/False for a Bool term over values that the rewriter did not fold; None otherwise.
    On an explicit stack, as a deep term would exhaust Python's recursion limit; an ite values
    only the branch its condition picks."""
    done = {}
    stack = [t]
    while stack:
        u = stack[-1]
        if u.id in done:
            stack.pop()
            continue
        kind = u.kind()
        children = u.children()
        if kind == Kind.NOT or kind in (Kind.AND, Kind.OR, Kind.XOR, Kind.IMPLIES):
            need = [c for c in children if c.id not in done]
        elif kind == Kind.ITE:
            if children[0].id not in done:
                need = [children[0]]
            else:
                c = done[children[0].id]
                branch = None if c is None else children[1] if c else children[2]
                need = [branch] if branch is not None and branch.id not in done else []
        else:
            need = []
        if need:
            stack.extend(reversed(need))
            continue
        stack.pop()
        done[u.id] = _ground_truth_of(u, kind, children, done)
    return done[t.id]


def _ground_truth_of(t, kind, children, done):
    """_ground_truth of t, its Boolean children's already in `done`."""
    if kind == Kind.NOT:
        v = done[children[0].id]
        return None if v is None else not v
    if kind in (Kind.AND, Kind.OR, Kind.XOR, Kind.IMPLIES):
        vs = [done[c.id] for c in children]
        if any(v is None for v in vs):
            return None
        if kind == Kind.AND:
            return all(vs)
        if kind == Kind.OR:
            return any(vs)
        if kind == Kind.XOR:
            return sum(vs) % 2 == 1
        return (not vs[0]) or vs[1]
    if kind in (Kind.EQUAL, Kind.DISTINCT):
        vs = [_ground_value(c) for c in children]
        if any(v is None for v in vs):
            return None
        same = lambda a, b: a.same(b) if isinstance(a, ExprRef) and isinstance(b, ExprRef) else a == b  # noqa: E731
        if kind == Kind.EQUAL:
            return same(vs[0], vs[1])
        return all(not same(vs[i], vs[j]) for i in range(len(vs)) for j in range(i + 1, len(vs)))
    if kind in (Kind.REAL_LT, Kind.REAL_LE, Kind.REAL_GT, Kind.REAL_GE):
        a, b = _ground_value(children[0]), _ground_value(children[1])
        if not (isinstance(a, Fraction) and isinstance(b, Fraction)):
            return None
        return {Kind.REAL_LT: a < b, Kind.REAL_LE: a <= b, Kind.REAL_GT: a > b, Kind.REAL_GE: a >= b}[kind]
    if kind == Kind.ITE:
        c = done[children[0].id]
        if c is None:
            return None
        return done[(children[1] if c else children[2]).id]
    return None


class BoolRef(ExprRef):
    def __invert__(self):
        return self._manager().mk_term(Kind.NOT, [self])

    def __and__(self, other):
        try:
            return _binop(Kind.AND, self, other)
        except _NoCoercion:
            return NotImplemented

    def __or__(self, other):
        try:
            return _binop(Kind.OR, self, other)
        except _NoCoercion:
            return NotImplemented

    def __xor__(self, other):
        try:
            return _binop(Kind.XOR, self, other)
        except _NoCoercion:
            return NotImplemented

    def __rand__(self, other):
        try:
            return _binop(Kind.AND, other, self)
        except _NoCoercion:
            return NotImplemented

    def __ror__(self, other):
        try:
            return _binop(Kind.OR, other, self)
        except _NoCoercion:
            return NotImplemented

    def __rxor__(self, other):
        try:
            return _binop(Kind.XOR, other, self)
        except _NoCoercion:
            return NotImplemented


class BoolNumRef(BoolRef):
    """A Bool value; bool(v) works."""

    def __bool__(self):
        return self.to_bool()

    def is_true(self):
        return self.to_bool()

    def is_false(self):
        return not self.to_bool()


def _bv_op(kind):
    def op(self, other):
        try:
            return _binop(kind, self, other)
        except _NoCoercion:
            return NotImplemented
    return op


def _bv_rop(kind):
    def rop(self, other):
        try:
            return _binop(kind, other, self)
        except _NoCoercion:
            return NotImplemented
    return rop


class BitVecRef(ExprRef):
    def size(self):
        return self.sort().size()

    __add__ = _bv_op(Kind.BV_ADD)
    __radd__ = _bv_rop(Kind.BV_ADD)
    __sub__ = _bv_op(Kind.BV_SUB)
    __rsub__ = _bv_rop(Kind.BV_SUB)
    __mul__ = _bv_op(Kind.BV_MUL)
    __rmul__ = _bv_rop(Kind.BV_MUL)
    __and__ = _bv_op(Kind.BV_AND)
    __rand__ = _bv_rop(Kind.BV_AND)
    __or__ = _bv_op(Kind.BV_OR)
    __ror__ = _bv_rop(Kind.BV_OR)
    __xor__ = _bv_op(Kind.BV_XOR)
    __rxor__ = _bv_rop(Kind.BV_XOR)
    __lshift__ = _bv_op(Kind.BV_SHL)
    __rlshift__ = _bv_rop(Kind.BV_SHL)
    # z3py conventions kept: signed comparisons and an arithmetic right shift
    __lt__ = _bv_op(Kind.BV_SLT)
    __le__ = _bv_op(Kind.BV_SLE)
    __gt__ = _bv_op(Kind.BV_SGT)
    __ge__ = _bv_op(Kind.BV_SGE)
    __rshift__ = _bv_op(Kind.BV_ASHR)
    __rrshift__ = _bv_rop(Kind.BV_ASHR)

    def __neg__(self):
        return self._manager().mk_term(Kind.BV_NEG, [self])

    def __invert__(self):
        return self._manager().mk_term(Kind.BV_NOT, [self])

    def __pos__(self):
        return self

    def __truediv__(self, other):
        raise TypeError("BV division is ambiguous: use UDiv/SDiv, URem/SRem/SMod")

    __rtruediv__ = __truediv__

    def __floordiv__(self, other):
        raise TypeError("BV division is ambiguous: use UDiv/SDiv, URem/SRem/SMod")

    __rfloordiv__ = __floordiv__

    def __mod__(self, other):
        raise TypeError("BV remainder is ambiguous: use URem/SRem/SMod")

    __rmod__ = __mod__

    def __pow__(self, other):
        raise TypeError("bit-vectors have no power operator")

    def __getitem__(self, i):
        raise TypeError("[] means select and applies to arrays only; a bit is Extract(i, i, x) or Bit(x, i)")


class BitVecNumRef(BitVecRef):
    """A bit-vector value."""

    def as_long(self):
        """The unsigned value."""
        return self.to_uint()

    def as_signed_long(self):
        """The two's complement value of size() bits."""
        return self.to_int()

    def as_binary_string(self):
        return self.to_bv_string(2, True)

    def as_hex_string(self):
        return self.to_bv_string(16, True)

    def as_string(self):
        return str(self.to_uint())

    def as_bytes(self, byteorder="little"):
        if byteorder not in ("little", "big"):
            raise ValueError("byteorder must be 'little' or 'big'")
        return self.to_bv_bytes(byteorder == "little")

    def __int__(self):
        return self.to_uint()

    def __index__(self):
        return self.to_uint()


def _fp_op(kind):
    def op(self, other):
        tm = self._manager()
        try:
            rm = tm.mk_rm(int(tm.default_rounding_mode))
            return _binop(kind, self, other, rm)
        except _NoCoercion:
            return NotImplemented
    return op


def _fp_rop(kind):
    def rop(self, other):
        tm = self._manager()
        try:
            rm = tm.mk_rm(int(tm.default_rounding_mode))
            return _binop(kind, other, self, rm)
        except _NoCoercion:
            return NotImplemented
    return rop


def _fp_cmp(kind):
    def op(self, other):
        try:
            return _binop(kind, self, other)
        except _NoCoercion:
            return NotImplemented
    return op


class FPRef(ExprRef):
    """A floating-point term. The arithmetic operators use the manager's default rounding
    mode; a float or int literal is converted exactly and rounded once under that mode.
    `==` is SMT '='; fpEQ is IEEE equality."""

    def ebits(self):
        return self.sort().ebits()

    def sbits(self):
        return self.sort().sbits()

    __add__ = _fp_op(Kind.FP_ADD)
    __radd__ = _fp_rop(Kind.FP_ADD)
    __sub__ = _fp_op(Kind.FP_SUB)
    __rsub__ = _fp_rop(Kind.FP_SUB)
    __mul__ = _fp_op(Kind.FP_MUL)
    __rmul__ = _fp_rop(Kind.FP_MUL)
    __truediv__ = _fp_op(Kind.FP_DIV)
    __rtruediv__ = _fp_rop(Kind.FP_DIV)
    __lt__ = _fp_cmp(Kind.FP_LT)
    __le__ = _fp_cmp(Kind.FP_LEQ)
    __gt__ = _fp_cmp(Kind.FP_GT)
    __ge__ = _fp_cmp(Kind.FP_GEQ)

    def __neg__(self):
        return self._manager().mk_term(Kind.FP_NEG, [self])

    def __abs__(self):
        return self._manager().mk_term(Kind.FP_ABS, [self])

    def __pos__(self):
        return self


class FPNumRef(FPRef):
    """A floating-point value."""

    def _fields(self):
        return self.to_fp()  # (exp_size, sig_size, sign, biased_exponent, cls, significand)

    def sign(self):
        return self._fields()[2]

    def exponent(self, biased=True):
        e = self._fields()[3]
        if biased:
            return e
        return e - ((1 << (self.ebits() - 1)) - 1)

    def exponent_as_long(self, biased=True):
        return self.exponent(biased)

    def significand(self):
        """The trailing sbits-1 significand bits, as an int of any width."""
        return self._fields()[5]

    def significand_as_long(self):
        return self.significand()

    def bits(self):
        """The ebits+sbits IEEE interchange bits."""
        return int(self.fp_bits(), 2)

    def _cls(self):
        return self._fields()[4]

    def isNaN(self):
        return self._cls() == _core.FP_NAN

    def isInf(self):
        return self._cls() == _core.FP_INFINITY

    def isZero(self):
        return self._cls() == _core.FP_ZERO

    def isNormal(self):
        return self._cls() == _core.FP_NORMAL

    def isSubnormal(self):
        return self._cls() == _core.FP_SUBNORMAL

    def isNegative(self):
        return self.sign()

    def isPositive(self):
        return not self.sign()

    def __float__(self):
        return self.fp_to_double()

    def as_fraction(self):
        """The exact rational value (finite values only; NotAValue for NaN and infinities)."""
        ebits, sbits, sign, exponent, c, significand = self._fields()
        if c in (_core.FP_NAN, _core.FP_INFINITY):
            raise NotAValue("%s has no rational value" % self.sexpr(), code=ErrorCode.NOT_A_VALUE,
                            function="FPNumRef.as_fraction")
        # Decode the binary fields directly. Decimal strings for binary128's
        # extremes exceed Python's integer-string digit limit.
        if c == _core.FP_NORMAL:
            significand |= 1 << (sbits - 1)
        power = max(exponent, 1) - ((1 << (ebits - 1)) - 1) - (sbits - 1)
        if sign:
            significand = -significand
        if power >= 0:
            return Fraction(significand << power)
        return Fraction(significand, 1 << -power)

    def as_string(self):
        return self.sexpr()


class RMRef(ExprRef):
    pass


class RMNumRef(RMRef):
    def as_rounding_mode(self):
        return RoundingMode(self.to_rm())


def _real_check(v):
    if isinstance(v, float):
        raise TypeError("a Python float cannot take sort Real: use Fraction, RealVal('%r') or Q(p, q)" % (v,))


def _real_op(kind):
    def op(self, other):
        _real_check(other)
        try:
            return _binop(kind, self, other)
        except _NoCoercion:
            return NotImplemented
    return op


def _real_rop(kind):
    def rop(self, other):
        _real_check(other)
        try:
            return _binop(kind, other, self)
        except _NoCoercion:
            return NotImplemented
    return rop


class RealRef(ExprRef):
    """A Real term (linear arithmetic). An int or a Fraction coerces; a float raises TypeError."""

    __add__ = _real_op(Kind.REAL_ADD)
    __radd__ = _real_rop(Kind.REAL_ADD)
    __sub__ = _real_op(Kind.REAL_SUB)
    __rsub__ = _real_rop(Kind.REAL_SUB)
    __mul__ = _real_op(Kind.REAL_MUL)
    __rmul__ = _real_rop(Kind.REAL_MUL)
    __truediv__ = _real_op(Kind.REAL_DIV)
    __rtruediv__ = _real_rop(Kind.REAL_DIV)
    __lt__ = _real_op(Kind.REAL_LT)
    __le__ = _real_op(Kind.REAL_LE)
    __gt__ = _real_op(Kind.REAL_GT)
    __ge__ = _real_op(Kind.REAL_GE)

    def __neg__(self):
        return self._manager().mk_term(Kind.REAL_NEG, [self])

    def __pos__(self):
        return self


class RatNumRef(RealRef):
    """A Real value (always a rational)."""

    def as_fraction(self):
        return Fraction(int(self.real_numerator()), int(self.real_denominator()))

    def numerator(self):
        return int(self.real_numerator())

    def denominator(self):
        return int(self.real_denominator())

    def numerator_as_long(self):
        return self.numerator()

    def denominator_as_long(self):
        return self.denominator()

    def as_decimal(self, prec):
        """A decimal string with `prec` digits after the point, truncated toward zero (z3py appends
        '?' when the expansion continues)."""
        if not _is_int(prec) or prec < 0:
            raise ArgumentError("as_decimal takes a count of digits, 0 or more (got %r)" % (prec,),
                                code=ErrorCode.INVALID_ARGUMENT)
        f = self.as_fraction()
        neg = f < 0
        f = abs(f)
        scaled = f * (10 ** prec)
        digits = scaled.numerator // scaled.denominator
        exact = scaled.denominator == 1 or scaled.numerator % scaled.denominator == 0
        s = str(digits).rjust(prec + 1, "0")
        if prec > 0:
            s = s[:-prec] + "." + s[-prec:]
        if not exact:
            s += "?"
        return ("-" if neg else "") + s

    def as_string(self):
        f = self.as_fraction()
        return str(f.numerator) if f.denominator == 1 else "%d/%d" % (f.numerator, f.denominator)

    def __float__(self):
        # correctly rounded, and OverflowError past the double range, as
        # float() of an int or a Fraction is
        return float(self.as_fraction())

    def is_int(self):
        return self.denominator() == 1


class ArrayRef(ExprRef):
    def domain(self):
        return self.sort().domain()

    def range(self):
        return self.sort().range()

    def __getitem__(self, i):
        return Select(self, i)


class ArrayNumRef(ArrayRef):
    """An array value: a term (a Store chain over K) that is also a read-only mapping view.
    v[i] for a value index is an explicit lookup (never via folding): the element if present,
    else the default; for a symbolic index it is Select(v, i). `i in v` means "has an explicit
    entry"."""

    _av = None  # the stp._core.ArrayValueHandle behind the view

    @classmethod
    def _from_value(cls, av):
        term = av.as_term()
        obj = term._manager().rewrap(term, cls)
        obj._av = av
        return obj

    @property
    def default(self):
        return self._av.default_value()

    def items(self):
        return [(idx, el) for idx, el in self._entries()]

    def keys(self):
        return [idx for idx, _ in self._entries()]

    def values(self):
        return [el for _, el in self._entries()]

    def _entries(self):
        return [self._av.entry(i) for i in range(self._av.size())]

    def __len__(self):
        return self._av.size()

    def _index_value(self, i):
        t = _coerce_arg(self.domain(), i)
        return t if t.is_value() else None

    def __getitem__(self, i):
        v = self._index_value(i)
        if v is None:
            return Select(self, i)
        return self._av.at(v)

    def __contains__(self, i):
        v = self._index_value(i)
        if v is None:
            return False
        return any(idx.same(v) for idx, _ in self._entries())

    def __iter__(self):
        return iter(self.keys())

    def as_bytes(self, first_index, count):
        """A dense read of `count` elements from `first_index`, little-endian bytes per element;
        the element width must be a multiple of 8."""
        elem = self.range()
        if elem.kind() != SortKind.BV or elem.size() % 8 != 0:
            raise ArgumentError("as_bytes needs a bit-vector element width that is a multiple of 8, not %r" % elem,
                                code=ErrorCode.INVALID_ARGUMENT, function="ArrayNumRef.as_bytes")
        n = elem.size() // 8
        out = bytearray()
        for k in range(count):
            out += self._av.at(_coerce_arg(self.domain(), first_index + k)).to_bv_bytes(True)[:n]
        return bytes(out)

    def as_term(self):
        return self

    def as_list(self):
        return self.items() + [self.default]


class FuncRef(ExprRef):
    """An uninterpreted function symbol; f(x, y) is APPLY, with the arity checked eagerly."""

    def arity(self):
        return self.sort().arity()

    def domain(self, i):
        return self.sort().domain(i)

    def range(self):
        return self.sort().range()

    def __call__(self, *args):
        sort = self.sort()
        n = sort.arity()
        if len(args) != n:
            raise ArgumentError("%s takes %d argument%s, %d given" % (self.decl_name() or "function", n,
                                                                       "" if n == 1 else "s", len(args)),
                                code=ErrorCode.ARITY, function="FuncRef.__call__")
        terms = [_coerce_arg(sort.domain(i), a) for i, a in enumerate(args)]
        return self._manager().mk_term(Kind.APPLY, [self] + terms)


class FuncEntry:
    """One case of a function interpretation: (arg values...) -> value."""

    def __init__(self, args, value):
        self._args = tuple(args)
        self._value = value

    def num_args(self):
        return len(self._args)

    def arg_value(self, i):
        return self._args[i]

    def value(self):
        return self._value

    def as_tuple(self):
        return (self._args, self._value)

    def __repr__(self):
        return "[%s, %s]" % (", ".join(str(a) for a in self._args), self._value)


class FuncInterp(_core.FunValueHandle):
    """A function in a saved model. Uninterpreted functions have entries and an else
    value; define-fun functions have a symbolic body. Both are callable; is_tabular()
    tells whether table inspection is supported."""

    def arity(self):
        return _core.FunValueHandle.arity(self)

    def else_value(self):
        return _core.FunValueHandle.else_value(self)

    def num_entries(self):
        return self.size()

    def entry(self, i):
        args, value = _core.FunValueHandle.entry(self, i)
        return FuncEntry(args, value)

    def entries(self):
        return [self.entry(i).as_tuple() for i in range(self.size())]

    def __len__(self):
        return self.size()

    def __iter__(self):
        return iter(self.entries())

    def __call__(self, *arg_values):
        sort = self.sort()
        n = sort.arity()
        if len(arg_values) != n:
            raise ArgumentError("the function takes %d argument%s, %d given" % (n, "" if n == 1 else "s", len(arg_values)),
                                code=ErrorCode.ARITY, function="FuncInterp.__call__")
        values = [_coerce_arg(sort.domain(i), a) for i, a in enumerate(arg_values)]
        return self.apply(values)

    def as_ite(self, *formals):
        return _core.FunValueHandle.as_ite(self, list(formals))

    def __repr__(self):
        if not self.is_tabular():
            return "<defined function %s>" % self.sort()
        parts = ["[%s -> %s]" % (", ".join(str(a) for a in args), value) for args, value in self.entries()]
        parts.append("else -> %s" % self.else_value())
        return "[" + ", ".join(parts) + "]"


class UninterpretedRef(ExprRef):
    pass


class UninterpretedNumRef(UninterpretedRef):
    @property
    def index(self):
        return self.to_uninterpreted_index()


_core.register_term_classes({
    SortKind.BOOL: (BoolRef, BoolNumRef),
    SortKind.BV: (BitVecRef, BitVecNumRef),
    SortKind.FP: (FPRef, FPNumRef),
    SortKind.RM: (RMRef, RMNumRef),
    SortKind.REAL: (RealRef, RatNumRef),
    SortKind.ARRAY: (ArrayRef, ArrayRef),
    SortKind.FUN: (FuncRef, FuncRef),
    SortKind.UNINTERPRETED: (UninterpretedRef, UninterpretedNumRef),
})
_core.register_value_classes(fun_value=FuncInterp)


# ---------------------------------------------------------------- declarations and values


def _names(names):
    if isinstance(names, str):
        return names.split()
    return list(names)


def Bool(name, tm=None, ctx=None):
    tm = _tm(tm, ctx)
    return tm.declare(name, tm.bool_sort())


def Bools(names, tm=None, ctx=None):
    return [Bool(n, tm, ctx) for n in _names(names)]


def BoolVal(v, tm=None, ctx=None):
    return _tm(tm, ctx).mk_bool(bool(v))


def BitVec(name, bits, tm=None, ctx=None):
    tm = _tm(tm, ctx)
    return tm.declare(name, tm.bv_sort(bits))


def BitVecs(names, bits, tm=None, ctx=None):
    return [BitVec(n, bits, tm, ctx) for n in _names(names)]


def BitVecVal(v, bits, *, wrap=False, tm=None, ctx=None):
    """A bit-vector literal. Strict: -2**(bits-1) <= v < 2**bits, else ArgumentError;
    wrap=True reduces v modulo 2**bits."""
    tm = _tm(tm, ctx)
    if isinstance(bits, BitVecSortRef):
        bits = bits.size()
    if not _is_int(v):
        if isinstance(v, bool):
            v = int(v)
        else:
            raise TypeError("BitVecVal takes an int, got %s" % type(v).__name__)
    if not _is_int(bits) or bits <= 0:
        raise ArgumentError("BitVecVal needs a positive width, got %r" % (bits,), code=ErrorCode.INVALID_ARGUMENT)
    if wrap:
        v %= (1 << bits)
    elif not (-(1 << (bits - 1)) <= v < (1 << bits)):
        raise ArgumentError("value %d does not fit %d bits (use wrap=True to wrap)" % (v, bits),
                            code=ErrorCode.VALUE_OUT_OF_RANGE, function="BitVecVal", argument_index=0)
    return tm.mk_bv(bits, v)


def FP(name, sort):
    _check_sort(sort, "FP")
    return sort.manager().declare(name, sort)


def FPs(names, sort):
    return [FP(n, sort) for n in _names(names)]


def FPVal(v, sort, rm=None):
    """A floating-point literal: a float's exact binary64 value or an int, rounded once to
    `sort` under rm (the manager's default); a str ("0.1", "1/3", "-2.5e-3") or a Fraction is
    an exact decimal/rational literal rounded once."""
    _check_sort(sort, "FPVal")
    if isinstance(rm, RMNumRef):
        rm = rm.as_rounding_mode()
    if isinstance(v, FPRef):
        if v.sort() == sort:
            return v
        raise SortMismatch("FPVal: %r has sort %r, not %r" % (v, v.sort(), sort), code=ErrorCode.SORT_MISMATCH)
    if isinstance(v, bool) or not isinstance(v, (int, float, str, Fraction)):
        raise TypeError("FPVal takes a float, an int, a str or a Fraction, got %s" % type(v).__name__)
    return _coerce(sort, v, rm)


def fpFromBits(bits, sort):
    _check_sort(sort, "fpFromBits")
    tm = sort.manager()
    if isinstance(bits, BitVecRef):
        return tm.mk_fp_from_bits(sort, bits)
    if not _is_int(bits):
        raise TypeError("fpFromBits takes an int or a bit-vector value")
    width = sort.ebits() + sort.sbits()
    if not (0 <= bits < (1 << width)):
        raise ArgumentError("bits %d do not fit %d bits" % (bits, width), code=ErrorCode.VALUE_OUT_OF_RANGE)
    return tm.mk_fp_from_bits_str(sort, "0b" + format(bits, "b").zfill(width))


def fpNaN(sort):
    _check_sort(sort, "fpNaN")
    return sort.manager().mk_fp_special(sort, "nan")


def fpPlusInfinity(sort):
    _check_sort(sort, "fpPlusInfinity")
    return sort.manager().mk_fp_special(sort, "+inf")


def fpMinusInfinity(sort):
    _check_sort(sort, "fpMinusInfinity")
    return sort.manager().mk_fp_special(sort, "-inf")


def fpInfinity(sort, negative):
    return fpMinusInfinity(sort) if negative else fpPlusInfinity(sort)


def fpPlusZero(sort):
    _check_sort(sort, "fpPlusZero")
    return sort.manager().mk_fp_special(sort, "+zero")


def fpMinusZero(sort):
    _check_sort(sort, "fpMinusZero")
    return sort.manager().mk_fp_special(sort, "-zero")


def fpZero(sort, negative):
    return fpMinusZero(sort) if negative else fpPlusZero(sort)


def fpFP(sign, exp, sig):
    for t in (sign, exp, sig):
        if not isinstance(t, BitVecRef):
            raise TypeError("fpFP takes three bit-vector terms (sign, exponent, significand)")
    return sign._manager().mk_term(Kind.FP_FP, [sign, exp, sig])


def RMVal(rm, tm=None, ctx=None):
    return _tm(tm, ctx).mk_rm(int(_rm_enum(rm)))


def RNE(tm=None, ctx=None):
    return RMVal(RoundingMode.RNE, tm, ctx)


def RNA(tm=None, ctx=None):
    return RMVal(RoundingMode.RNA, tm, ctx)


def RTP(tm=None, ctx=None):
    return RMVal(RoundingMode.RTP, tm, ctx)


def RTN(tm=None, ctx=None):
    return RMVal(RoundingMode.RTN, tm, ctx)


def RTZ(tm=None, ctx=None):
    return RMVal(RoundingMode.RTZ, tm, ctx)


RoundNearestTiesToEven = RNE
RoundNearestTiesToAway = RNA
RoundTowardPositive = RTP
RoundTowardNegative = RTN
RoundTowardZero = RTZ


def Real(name, tm=None, ctx=None):
    tm = _tm(tm, ctx)
    return tm.declare(name, tm.real_sort())


def Reals(names, tm=None, ctx=None):
    return [Real(n, tm, ctx) for n in _names(names)]


def RealVal(v, tm=None, ctx=None):
    """A Real literal from an int, a Fraction or a str ("-3/7", "0.25", "12"); a float raises."""
    tm = _tm(tm, ctx)
    if isinstance(v, RealRef):
        return v
    if isinstance(v, float):
        raise TypeError("RealVal(%r): a Python float is not exact; pass a str ('%r'), a Fraction or Q(p, q)" % (v, v))
    if isinstance(v, bool) or not isinstance(v, (int, str, Fraction)):
        raise TypeError("RealVal takes an int, a Fraction or a str, got %s" % type(v).__name__)
    return _coerce(tm.real_sort(), v)


def Q(numerator, denominator, tm=None, ctx=None):
    if not (_is_int(numerator) and _is_int(denominator)):
        raise TypeError("Q takes two ints")
    if denominator < 0:  # the sign goes with the numerator: Q(1, -2) is -1/2
        numerator, denominator = -numerator, -denominator
    return _tm(tm, ctx).mk_real_str("%d/%d" % (numerator, denominator))


def Array(name, index, element):
    return index.manager().declare(name, ArraySort(index, element))


def K(sort, element):
    """A constant array. K(ArraySort(I, E), literal_or_value) coerces the literal by the array's
    element sort; K(index_sort, value) is z3py's form (the range sort is the value's). The
    element must be a value, a term with no symbol in it: anything else raises Unsupported."""
    _check_sort(sort, "K")
    if isinstance(sort, ArraySortRef):
        elem = _coerce_arg(sort.range(), element)
        return _wrap_const_array(sort.manager().mk_const_array(sort, elem))
    if not isinstance(element, ExprRef):
        raise TypeError("K(index_sort, element) needs a term element (the array's range is its sort)")
    asort = ArraySort(sort, element.sort())
    return _wrap_const_array(sort.manager().mk_const_array(asort, element))


def _wrap_const_array(t):
    return t


def ArrayFromBytes(data, index_bits=32, tm=None, ctx=None):
    """A Store chain over K(ArraySort(BitVecSort(index_bits), BitVecSort(8)), 0) holding `data`
    (bytes or a bytes-like object)."""
    return _tm(tm, ctx).array_from_bytes(data, index_bits)


def Function(name, *domain_then_range):
    fs = FuncSort(*domain_then_range)
    return fs.manager().declare(name, fs)


def Const(name, sort):
    _check_sort(sort, "Const")
    return sort.manager().declare(name, sort)


def Consts(names, sort):
    return [Const(n, sort) for n in _names(names)]


def FreshConst(sort, prefix="c"):
    _check_sort(sort, "FreshConst")
    return sort.manager().mk_fresh(sort, prefix)


def FreshBool(prefix="b", tm=None, ctx=None):
    tm = _tm(tm, ctx)
    return tm.mk_fresh(tm.bool_sort(), prefix)


def FreshBitVec(bits, prefix="x", tm=None, ctx=None):
    tm = _tm(tm, ctx)
    return tm.mk_fresh(tm.bv_sort(bits), prefix)


# ---------------------------------------------------------------- operators as functions


def _flatten_bools(args):
    out = []
    for a in args:
        if isinstance(a, ExprRef) or isinstance(a, bool):
            out.append(a)
        elif isinstance(a, (list, tuple, set, frozenset)) or hasattr(a, "__iter__") and not isinstance(a, (str, bytes)):
            out.extend(_flatten_bools(list(a)))
        else:
            out.append(a)
    return out


def _bools(args, where):
    args = _flatten_bools(args)
    t = _term_of(args, where)
    tm = t._manager() if t is not None else main_tm()
    b = tm.bool_sort()
    return tm, [_coerce_arg(b, a) for a in args]


def And(*args):
    tm, ts = _bools(args, "And")
    if not ts:
        return tm.mk_bool(True)
    if len(ts) == 1:
        return ts[0]
    return tm.mk_term(Kind.AND, ts)


def Or(*args):
    tm, ts = _bools(args, "Or")
    if not ts:
        return tm.mk_bool(False)
    if len(ts) == 1:
        return ts[0]
    return tm.mk_term(Kind.OR, ts)


def Not(a):
    tm, ts = _bools([a], "Not")
    return tm.mk_term(Kind.NOT, ts)


def Xor(*args):
    tm, ts = _bools(args, "Xor")
    if len(ts) < 2:
        raise ArgumentError("Xor takes at least two arguments", code=ErrorCode.ARITY)
    return tm.mk_term(Kind.XOR, ts)


def Implies(a, b):
    tm, ts = _bools([a, b], "Implies")
    return tm.mk_term(Kind.IMPLIES, ts)


def If(c, t, e):
    # the condition's manager, or under a Python bool the branches'
    first = _term_of([c, t, e], "If")
    tm = first._manager() if first is not None else main_tm()
    c = _coerce_arg(tm.bool_sort(), c)
    if isinstance(t, ExprRef):
        e = _coerce_arg(t.sort(), e)
    elif isinstance(e, ExprRef):
        t = _coerce_arg(e.sort(), t)
    else:
        raise TypeError("If: at least one branch must be a term (both are Python literals)")
    return tm.mk_term(Kind.ITE, [c, t, e])


def Distinct(*args):
    if len(args) == 1 and isinstance(args[0], (list, tuple)):
        args = tuple(args[0])
    t = _term_of(args, "Distinct")
    if t is None:
        raise TypeError("Distinct needs at least one term")
    ts = [_coerce_arg(t.sort(), a) for a in args]
    if len(ts) < 2:
        return t._manager().mk_bool(True)
    return t._manager().mk_term(Kind.DISTINCT, ts)


def _arith_nary(args, bv_kind, real_kind, name, unit):
    if len(args) == 1 and isinstance(args[0], (list, tuple)):
        args = tuple(args[0])
    t = _term_of(args, name)
    if t is None:
        if not args:
            raise TypeError("%s() needs at least one term" % name)
        raise TypeError("%s of Python numbers only: nothing tells their sort" % name)
    sort = t.sort()
    k = sort.kind()
    if k == SortKind.BV:
        kind = bv_kind
    elif k == SortKind.REAL:
        kind = real_kind
    else:
        raise TypeError("%s takes bit-vector or Real terms, not %r" % (name, sort))
    ts = [_coerce_arg(sort, a) for a in args]
    if len(ts) == 1:
        return ts[0]
    if k == SortKind.REAL and kind == Kind.REAL_MUL:
        # REAL_MUL is binary (linear: one side a value); fold left
        acc = ts[0]
        for u in ts[1:]:
            acc = t._manager().mk_term(kind, [acc, u])
        return acc
    return t._manager().mk_term(kind, ts)


def Sum(*args):
    return _arith_nary(args, Kind.BV_ADD, Kind.REAL_ADD, "Sum", 0)


def Product(*args):
    return _arith_nary(args, Kind.BV_MUL, Kind.REAL_MUL, "Product", 1)


def _bv2(kind, a, b, name):
    if not (isinstance(a, BitVecRef) or isinstance(b, BitVecRef)):
        raise TypeError("%s takes bit-vector terms" % name)
    return _binop(kind, a, b)


def ULT(a, b):
    return _bv2(Kind.BV_ULT, a, b, "ULT")


def ULE(a, b):
    return _bv2(Kind.BV_ULE, a, b, "ULE")


def UGT(a, b):
    return _bv2(Kind.BV_UGT, a, b, "UGT")


def UGE(a, b):
    return _bv2(Kind.BV_UGE, a, b, "UGE")


def UDiv(a, b):
    return _bv2(Kind.BV_UDIV, a, b, "UDiv")


def URem(a, b):
    return _bv2(Kind.BV_UREM, a, b, "URem")


def SDiv(a, b):
    return _bv2(Kind.BV_SDIV, a, b, "SDiv")


def SRem(a, b):
    return _bv2(Kind.BV_SREM, a, b, "SRem")


def SMod(a, b):
    return _bv2(Kind.BV_SMOD, a, b, "SMod")


def LShR(a, b):
    return _bv2(Kind.BV_LSHR, a, b, "LShR")


def SLT(a, b):
    return _bv2(Kind.BV_SLT, a, b, "SLT")


def SLE(a, b):
    return _bv2(Kind.BV_SLE, a, b, "SLE")


def SGT(a, b):
    return _bv2(Kind.BV_SGT, a, b, "SGT")


def SGE(a, b):
    return _bv2(Kind.BV_SGE, a, b, "SGE")


def _bv1(a, name):
    if not isinstance(a, BitVecRef):
        raise TypeError("%s takes a bit-vector term" % name)
    return a


def Extract(hi, lo, a):
    _bv1(a, "Extract")
    if not (_is_int(hi) and _is_int(lo)):
        raise TypeError("Extract(hi, lo, a): hi and lo are ints")
    return a._manager().mk_term(Kind.BV_EXTRACT, [a], (hi, lo))


def Bit(a, i):
    """(= ((_ extract i i) a) #b1)"""
    _bv1(a, "Bit")
    return Extract(i, i, a) == 1


def BoolToBV1(b):
    tm, bs = _bools([b], "BoolToBV1")
    return If(bs[0], tm.mk_bv(1, 1), tm.mk_bv(1, 0))


def BV1ToBool(a):
    _bv1(a, "BV1ToBool")
    return a == 1


def Concat(*args):
    if len(args) == 1 and isinstance(args[0], (list, tuple)):
        args = tuple(args[0])
    if not args:
        raise ArgumentError("Concat needs at least one term", code=ErrorCode.ARITY)
    for a in args:
        _bv1(a, "Concat")
    if len(args) == 1:
        return args[0]
    return args[0]._manager().mk_term(Kind.BV_CONCAT, list(args))


def ZeroExt(k, a):
    _bv1(a, "ZeroExt")
    return a._manager().mk_term(Kind.BV_ZERO_EXTEND, [a], (k,))


def SignExt(k, a):
    _bv1(a, "SignExt")
    return a._manager().mk_term(Kind.BV_SIGN_EXTEND, [a], (k,))


def RepeatBitVec(n, a):
    _bv1(a, "RepeatBitVec")
    return a._manager().mk_term(Kind.BV_REPEAT, [a], (n,))


RepeatBV = RepeatBitVec


def RotateLeft(a, b):
    """z3py order: the term first; an int amount is the indexed kind, a term amount is
    taken modulo the size, as an int amount is: (a << r) | LShR(a, size - r) with
    r = URem(b, size)."""
    _bv1(a, "RotateLeft")
    if _is_int(b):
        return a._manager().mk_term(Kind.BV_ROTATE_LEFT, [a], (b % a.size() if a.size() else 0,))
    b = _coerce_arg(a.sort(), b)
    n = a.size()
    size = BitVecVal(n, n, wrap=True, tm=a._manager())
    r = URem(b, size)
    return (a << r) | LShR(a, size - r)


def RotateRight(a, b):
    _bv1(a, "RotateRight")
    if _is_int(b):
        return a._manager().mk_term(Kind.BV_ROTATE_RIGHT, [a], (b % a.size() if a.size() else 0,))
    b = _coerce_arg(a.sort(), b)
    n = a.size()
    size = BitVecVal(n, n, wrap=True, tm=a._manager())
    r = URem(b, size)
    return LShR(a, r) | (a << (size - r))


def BVComp(a, b):
    return _bv2(Kind.BV_COMP, a, b, "BVComp")


def BVNand(a, b):
    return _bv2(Kind.BV_NAND, a, b, "BVNand")


def BVNor(a, b):
    return _bv2(Kind.BV_NOR, a, b, "BVNor")


def BVXnor(a, b):
    return _bv2(Kind.BV_XNOR, a, b, "BVXnor")


def BVRedAnd(a):
    _bv1(a, "BVRedAnd")
    return a._manager().mk_term(Kind.BV_REDAND, [a])


def BVRedOr(a):
    _bv1(a, "BVRedOr")
    return a._manager().mk_term(Kind.BV_REDOR, [a])


def bvuaddo(a, b):
    return _bv2(Kind.BV_UADDO, a, b, "bvuaddo")


def bvsaddo(a, b):
    return _bv2(Kind.BV_SADDO, a, b, "bvsaddo")


def bvumulo(a, b):
    return _bv2(Kind.BV_UMULO, a, b, "bvumulo")


def bvsmulo(a, b):
    return _bv2(Kind.BV_SMULO, a, b, "bvsmulo")


def bvusubo(a, b):
    return _bv2(Kind.BV_USUBO, a, b, "bvusubo")


def bvssubo(a, b):
    return _bv2(Kind.BV_SSUBO, a, b, "bvssubo")


def bvnego(a):
    _bv1(a, "bvnego")
    return a._manager().mk_term(Kind.BV_NEGO, [a])


def bvsdivo(a, b):
    return _bv2(Kind.BV_SDIVO, a, b, "bvsdivo")


def _signed_pair(a, b, name):
    if not (isinstance(a, BitVecRef) or isinstance(b, BitVecRef)):
        raise TypeError("%s takes bit-vector terms" % name)
    if isinstance(a, BitVecRef):
        b = _coerce_arg(a.sort(), b)
    else:
        a = _coerce_arg(b.sort(), a)
    return a, b


def BVAddNoOverflow(a, b, signed):
    """z3py: the addition does not overflow (unsigned: no wrap; signed: not beyond the maximum)."""
    a, b = _signed_pair(a, b, "BVAddNoOverflow")
    if not signed:
        return Not(bvuaddo(a, b))
    return Not(And(a >= 0, b >= 0, (a + b) < 0))


def BVAddNoUnderflow(a, b):
    """The signed addition does not go below the minimum."""
    a, b = _signed_pair(a, b, "BVAddNoUnderflow")
    return Not(And(a < 0, b < 0, (a + b) >= 0))


def BVSubNoOverflow(a, b):
    """The signed subtraction does not exceed the maximum."""
    a, b = _signed_pair(a, b, "BVSubNoOverflow")
    return Not(And(a >= 0, b < 0, (a - b) < 0))


def BVSubNoUnderflow(a, b, signed):
    a, b = _signed_pair(a, b, "BVSubNoUnderflow")
    if not signed:
        return UGE(a, b)
    return Not(And(a < 0, b > 0, (a - b) >= 0))


def BVMulNoOverflow(a, b, signed):
    a, b = _signed_pair(a, b, "BVMulNoOverflow")
    if not signed:
        return Not(bvumulo(a, b))
    # a signed product exceeds the maximum only when the true product is positive
    return Not(And(bvsmulo(a, b), Not(Xor(a < 0, b < 0))))


def BVMulNoUnderflow(a, b):
    a, b = _signed_pair(a, b, "BVMulNoUnderflow")
    return Not(And(bvsmulo(a, b), Xor(a < 0, b < 0)))


def BVSNegNoOverflow(a):
    return Not(bvnego(a))


def BVSDivNoOverflow(a, b):
    return Not(bvsdivo(a, b))


def Select(a, i):
    if not isinstance(a, ArrayRef):
        raise TypeError("Select takes an array term, got %s" % type(a).__name__)
    i = _coerce_arg(a.domain(), i)
    return a._manager().mk_term(Kind.SELECT, [a, i])


def Store(a, i, v):
    if not isinstance(a, ArrayRef):
        raise TypeError("Store takes an array term, got %s" % type(a).__name__)
    i = _coerce_arg(a.domain(), i)
    v = _coerce_arg(a.range(), v)
    return a._manager().mk_term(Kind.STORE, [a, i, v])


Update = Store


def Default(a):
    """The default element of an array value (z3py name)."""
    if isinstance(a, ArrayNumRef):
        return a.default
    if isinstance(a, ArrayRef) and a.kind() == Kind.CONST_ARRAY:
        return a.arg(0)
    raise TypeError("Default takes an array value")


def _fp1(a, name):
    if not isinstance(a, FPRef):
        raise TypeError("%s takes a floating-point term" % name)
    return a


def _rm_term(rm, tm):
    if isinstance(rm, RMRef):
        return rm
    return tm.mk_rm(int(_rm_enum(rm)))


def _fp_rm_binary(kind, rm, a, b, name):
    if isinstance(a, FPRef):
        tm = a._manager()
    elif isinstance(b, FPRef):
        tm = b._manager()
    else:
        raise TypeError("%s takes floating-point terms" % name)
    rmt = _rm_term(rm, tm)
    mode = rmt.as_rounding_mode() if isinstance(rmt, RMNumRef) else None
    if isinstance(a, FPRef):
        b = _coerce_arg(a.sort(), b, mode)
    else:
        a = _coerce_arg(b.sort(), a, mode)
    return tm.mk_term(kind, [rmt, a, b])


def fpAbs(a):
    _fp1(a, "fpAbs")
    return a._manager().mk_term(Kind.FP_ABS, [a])


def fpNeg(a):
    _fp1(a, "fpNeg")
    return a._manager().mk_term(Kind.FP_NEG, [a])


def fpAdd(rm, a, b):
    """fp.add under rm; a literal operand is rounded under THIS call's mode."""
    return _fp_rm_binary(Kind.FP_ADD, rm, a, b, "fpAdd")


def fpSub(rm, a, b):
    return _fp_rm_binary(Kind.FP_SUB, rm, a, b, "fpSub")


def fpMul(rm, a, b):
    return _fp_rm_binary(Kind.FP_MUL, rm, a, b, "fpMul")


def fpDiv(rm, a, b):
    return _fp_rm_binary(Kind.FP_DIV, rm, a, b, "fpDiv")


def fpFMA(rm, a, b, c):
    _fp1(a, "fpFMA")
    tm = a._manager()
    rmt = _rm_term(rm, tm)
    mode = rmt.as_rounding_mode() if isinstance(rmt, RMNumRef) else None
    return tm.mk_term(Kind.FP_FMA, [rmt, a, _coerce_arg(a.sort(), b, mode), _coerce_arg(a.sort(), c, mode)])


def fpSqrt(rm, a):
    _fp1(a, "fpSqrt")
    return a._manager().mk_term(Kind.FP_SQRT, [_rm_term(rm, a._manager()), a])


def fpRem(a, b):
    _fp1(a, "fpRem")
    return a._manager().mk_term(Kind.FP_REM, [a, _coerce_arg(a.sort(), b)])


def fpRoundToIntegral(rm, a):
    _fp1(a, "fpRoundToIntegral")
    return a._manager().mk_term(Kind.FP_RTI, [_rm_term(rm, a._manager()), a])


def fpMin(a, b):
    _fp1(a, "fpMin")
    return a._manager().mk_term(Kind.FP_MIN, [a, _coerce_arg(a.sort(), b)])


def fpMax(a, b):
    _fp1(a, "fpMax")
    return a._manager().mk_term(Kind.FP_MAX, [a, _coerce_arg(a.sort(), b)])


def _fp_cmp2(kind, a, b, name):
    if isinstance(a, FPRef):
        b = _coerce_arg(a.sort(), b)
    elif isinstance(b, FPRef):
        a = _coerce_arg(b.sort(), a)
    else:
        raise TypeError("%s takes floating-point terms" % name)
    return a._manager().mk_term(kind, [a, b])


def fpEQ(a, b):
    """IEEE equality (fp.eq); `==` is SMT '='."""
    return _fp_cmp2(Kind.FP_EQ, a, b, "fpEQ")


def fpNEQ(a, b):
    return Not(fpEQ(a, b))


def fpLT(a, b):
    return _fp_cmp2(Kind.FP_LT, a, b, "fpLT")


def fpLEQ(a, b):
    return _fp_cmp2(Kind.FP_LEQ, a, b, "fpLEQ")


def fpGT(a, b):
    return _fp_cmp2(Kind.FP_GT, a, b, "fpGT")


def fpGEQ(a, b):
    return _fp_cmp2(Kind.FP_GEQ, a, b, "fpGEQ")


def _fp_pred(kind, name):
    def pred(a):
        _fp1(a, name)
        return a._manager().mk_term(kind, [a])
    pred.__name__ = name
    return pred


fpIsNaN = _fp_pred(Kind.FP_IS_NAN, "fpIsNaN")
fpIsInf = _fp_pred(Kind.FP_IS_INF, "fpIsInf")
fpIsZero = _fp_pred(Kind.FP_IS_ZERO, "fpIsZero")
fpIsNormal = _fp_pred(Kind.FP_IS_NORMAL, "fpIsNormal")
fpIsSubnormal = _fp_pred(Kind.FP_IS_SUBNORMAL, "fpIsSubnormal")
fpIsNegative = _fp_pred(Kind.FP_IS_NEG, "fpIsNegative")
fpIsPositive = _fp_pred(Kind.FP_IS_POS, "fpIsPositive")


def _fp_target(sort, name):
    if not isinstance(sort, FPSortRef):
        raise TypeError("%s: the target must be a floating-point sort, got %r" % (name, sort))
    return (sort.ebits(), sort.sbits())


def fpToFP(rm, x, sort):
    """(_ to_fp e s) by argument sort: another format, a signed bit-vector or a Real value."""
    idx = _fp_target(sort, "fpToFP")
    if isinstance(x, FPRef):
        kind = Kind.FP_TO_FP_FROM_FP
    elif isinstance(x, BitVecRef):
        kind = Kind.FP_TO_FP_FROM_SBV
    elif isinstance(x, RealRef):
        kind = Kind.FP_TO_FP_FROM_REAL
    else:
        raise TypeError("fpToFP converts a floating-point, bit-vector or Real term, got %s" % type(x).__name__)
    tm = x._manager()
    return tm.mk_term(kind, [_rm_term(rm, tm), x], idx)


def fpFPToFP(rm, x, sort):
    _fp1(x, "fpFPToFP")
    return fpToFP(rm, x, sort)


def fpBVToFP(bv, sort):
    """The reinterpretation of the bits."""
    _bv1(bv, "fpBVToFP")
    return bv._manager().mk_term(Kind.FP_TO_FP_FROM_BV, [bv], _fp_target(sort, "fpBVToFP"))


def fpSignedToFP(rm, bv, sort):
    _bv1(bv, "fpSignedToFP")
    tm = bv._manager()
    return tm.mk_term(Kind.FP_TO_FP_FROM_SBV, [_rm_term(rm, tm), bv], _fp_target(sort, "fpSignedToFP"))


def fpUnsignedToFP(rm, bv, sort):
    _bv1(bv, "fpUnsignedToFP")
    tm = bv._manager()
    return tm.mk_term(Kind.FP_TO_FP_FROM_UBV, [_rm_term(rm, tm), bv], _fp_target(sort, "fpUnsignedToFP"))


def fpRealToFP(rm, r, sort):
    if not isinstance(r, RealRef):
        r = RealVal(r, tm=sort.manager())
    tm = r._manager()
    return tm.mk_term(Kind.FP_TO_FP_FROM_REAL, [_rm_term(rm, tm), r], _fp_target(sort, "fpRealToFP"))


def _bits_of(sort_or_bits, name):
    if isinstance(sort_or_bits, BitVecSortRef):
        return sort_or_bits.size()
    if _is_int(sort_or_bits):
        return sort_or_bits
    raise TypeError("%s: the target is a bit-vector sort or a width" % name)


def fpToSBV(rm, x, sort_or_bits):
    _fp1(x, "fpToSBV")
    tm = x._manager()
    return tm.mk_term(Kind.FP_TO_SBV, [_rm_term(rm, tm), x], (_bits_of(sort_or_bits, "fpToSBV"),))


def fpToUBV(rm, x, sort_or_bits):
    _fp1(x, "fpToUBV")
    tm = x._manager()
    return tm.mk_term(Kind.FP_TO_UBV, [_rm_term(rm, tm), x], (_bits_of(sort_or_bits, "fpToUBV"),))


def fpToIEEEBV(x):
    _fp1(x, "fpToIEEEBV")
    return x._manager().mk_term(Kind.FP_TO_IEEE_BV, [x])


def fpToReal(x):
    _fp1(x, "fpToReal")
    return x._manager().mk_term(Kind.FP_TO_REAL, [x])


def simplify(t):
    if not isinstance(t, ExprRef):
        raise TypeError("simplify takes a term")
    return t._manager().simplify_term(t)


def substitute(t, *pairs):
    if not isinstance(t, ExprRef):
        raise TypeError("substitute takes a term")
    return t.substitute(*pairs)


def is_expr(t):
    return isinstance(t, ExprRef)


def is_app(t):
    return isinstance(t, ExprRef)


def is_const(t):
    """z3py's meaning: a symbol or a value (0-ary)."""
    return isinstance(t, ExprRef) and t.num_children() == 0 and t.kind() in (Kind.CONSTANT, Kind.VALUE)


def is_symbol(t):
    return isinstance(t, ExprRef) and t.is_const()


def is_value(t):
    return isinstance(t, ExprRef) and t.is_value()


def is_true(t):
    return isinstance(t, BoolNumRef) and t.to_bool()


def is_false(t):
    return isinstance(t, BoolNumRef) and not t.to_bool()


def is_bool(t):
    return isinstance(t, BoolRef)


def is_bv(t):
    return isinstance(t, BitVecRef)


def is_bv_value(t):
    return isinstance(t, BitVecNumRef)


def is_fp(t):
    return isinstance(t, FPRef)


def is_fp_value(t):
    return isinstance(t, FPNumRef)


def is_real(t):
    return isinstance(t, RealRef)


def is_rational_value(t):
    return isinstance(t, RatNumRef)


def is_array(t):
    return isinstance(t, ArrayRef)


def is_func_decl(t):
    return isinstance(t, FuncRef)


def is_rm(t):
    return isinstance(t, RMRef)


def is_sort(s):
    return isinstance(s, SortRef)
