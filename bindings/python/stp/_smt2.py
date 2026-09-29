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

"""Rebuilding terms, sorts and models: pickling, translate(tm) across managers, and
Model.from_smt2. Terms travel as their public structure (kind, indices, children,
values, symbol declarations) and are rebuilt through the name table of the target
manager; the SMT-LIB text of a model is read by a small s-expression reader and the
values are constructed through the API (the parser does not read back the S!k spelling
of a value of a declared sort)."""

import re
from fractions import Fraction

from . import _core
from ._gen_kinds import Kind, ErrorCode
from ._core import ArgumentError, Unsupported, SortMismatch, ParseError, StateError

# ---------------------------------------------------------------- sorts as text

_SIMPLE_SYMBOL = re.compile(r"^[A-Za-z~!@$%^&*_+=<>.?/-][A-Za-z0-9~!@$%^&*_+=<>.?/-]*$")


def quote_symbol(name):
    if _SIMPLE_SYMBOL.match(name) and not name[0].isdigit():
        return name
    return "|" + name + "|"


def unquote_symbol(name):
    if len(name) >= 2 and name[0] == "|" and name[-1] == "|":
        return name[1:-1]
    return name


def sort_text(sort):
    """SMT-LIB 2 text of a sort; a function sort as (-> (D...) R) (no standard spelling)."""
    from ._terms import SortKind
    k = sort.kind()
    if k == SortKind.FUN:
        return "(-> (%s) %s)" % (" ".join(sort_text(sort.domain(i)) for i in range(sort.arity())), sort_text(sort.range()))
    if k == SortKind.UNINTERPRETED:
        return quote_symbol(sort.name())
    return sort.sexpr()


def parse_sort(text_or_sexpr, tm):
    """A sort of tm from its text (or an already tokenised s-expression)."""
    sx = text_or_sexpr if isinstance(text_or_sexpr, (list, str)) and not isinstance(text_or_sexpr, str) \
        else read_sexpr(text_or_sexpr)
    return _sort_of(sx, tm)


def _sort_of(sx, tm):
    if isinstance(sx, str):
        if sx == "Bool":
            return tm.bool_sort()
        if sx == "Real":
            return tm.real_sort()
        if sx == "RoundingMode":
            return tm.rm_sort()
        if sx == "Float16":
            return tm.fp_sort(5, 11)
        if sx == "Float32":
            return tm.fp_sort(8, 24)
        if sx == "Float64":
            return tm.fp_sort(11, 53)
        if sx == "Float128":
            return tm.fp_sort(15, 113)
        return tm.declare_sort(unquote_symbol(sx))
    if not sx:
        raise ParseError("empty sort", code=ErrorCode.PARSE)
    head = sx[0]
    if head == "_" and len(sx) == 3 and sx[1] == "BitVec":
        return tm.bv_sort(int(sx[2]))
    if head == "_" and len(sx) == 4 and sx[1] == "FloatingPoint":
        return tm.fp_sort(int(sx[2]), int(sx[3]))
    if head == "Array" and len(sx) == 3:
        return tm.array_sort(_sort_of(sx[1], tm), _sort_of(sx[2], tm))
    if head == "->" and len(sx) == 3:
        return tm.fun_sort([_sort_of(d, tm) for d in sx[1]], _sort_of(sx[2], tm))
    raise ParseError("unknown sort %s" % write_sexpr(sx), code=ErrorCode.PARSE)


def unpickle_sort(text):
    from ._terms import main_tm
    return parse_sort(text, main_tm())


def translate_sort(sort, tm):
    return parse_sort(sort_text(sort), tm)


# ---------------------------------------------------------------- s-expressions

_TOKEN = re.compile(r'\s+|;[^\n]*|\|[^|]*\||"(?:[^"]|"")*"|[()]|[^\s()|"]+')


def tokenize(text):
    out = []
    pos = 0
    n = len(text)
    while pos < n:
        m = _TOKEN.match(text, pos)
        if m is None:
            raise ParseError("unexpected character %r at offset %d" % (text[pos], pos), code=ErrorCode.PARSE)
        tok = m.group(0)
        pos = m.end()
        if tok.isspace() or tok.startswith(";"):
            continue
        out.append(tok)
    return out


def read_sexpr(text):
    """One s-expression as nested lists of token strings."""
    exprs = read_all(text)
    if len(exprs) != 1:
        raise ParseError("expected one s-expression, found %d" % len(exprs), code=ErrorCode.PARSE)
    return exprs[0]


def read_all(text):
    toks = tokenize(text)
    out = []
    stack = []
    for tok in toks:
        if tok == "(":
            stack.append([])
        elif tok == ")":
            if not stack:
                raise ParseError("unbalanced ')'", code=ErrorCode.PARSE)
            done = stack.pop()
            if stack:
                stack[-1].append(done)
            else:
                out.append(done)
        else:
            if stack:
                stack[-1].append(tok)
            else:
                out.append(tok)
    if stack:
        raise ParseError("unbalanced '('", code=ErrorCode.PARSE)
    return out


def write_sexpr(sx):
    if isinstance(sx, str):
        return sx
    return "(" + " ".join(write_sexpr(x) for x in sx) + ")"


# ---------------------------------------------------------------- values from text

_RM_NAMES = {
    "RNE": _core.RM_RNE, "roundNearestTiesToEven": _core.RM_RNE,
    "RNA": _core.RM_RNA, "roundNearestTiesToAway": _core.RM_RNA,
    "RTP": _core.RM_RTP, "roundTowardPositive": _core.RM_RTP,
    "RTN": _core.RM_RTN, "roundTowardNegative": _core.RM_RTN,
    "RTZ": _core.RM_RTZ, "roundTowardZero": _core.RM_RTZ,
}


def value_of(sx, sort, tm):
    """The value term of `sort` written as the s-expression sx (the printer's forms)."""
    from ._terms import SortKind
    k = sort.kind()
    if k == SortKind.BOOL:
        if sx == "true":
            return tm.mk_bool(True)
        if sx == "false":
            return tm.mk_bool(False)
    elif k == SortKind.BV:
        if isinstance(sx, str):
            if sx.startswith("#x"):
                return tm.mk_bv_str(sort.size(), sx[2:], 16)
            if sx.startswith("#b"):
                return tm.mk_bv_str(sort.size(), sx[2:], 2)
            if sx.isdigit():
                return tm.mk_bv_str(sort.size(), sx, 10)
        elif len(sx) == 3 and sx[0] == "_" and isinstance(sx[1], str) and sx[1].startswith("bv"):
            return tm.mk_bv_str(sort.size(), sx[1][2:], 10)
    elif k == SortKind.FP:
        if isinstance(sx, list):
            if len(sx) == 4 and sx[0] == "fp":
                bits = "".join(_bits(part) for part in sx[1:])
                return tm.mk_fp_from_bits_str(sort, "0b" + bits)
            if len(sx) == 4 and sx[0] == "_":
                which = {"+zero": "+zero", "-zero": "-zero", "+oo": "+inf", "-oo": "-inf", "NaN": "nan"}.get(sx[1])
                if which is not None:
                    return tm.mk_fp_special(sort, which)
    elif k == SortKind.RM:
        if isinstance(sx, str) and sx in _RM_NAMES:
            return tm.mk_rm(_RM_NAMES[sx])
    elif k == SortKind.REAL:
        f = _rational_of(sx)
        if f is not None:
            return tm.mk_real_str(str(f.numerator) if f.denominator == 1 else "%d/%d" % (f.numerator, f.denominator))
    elif k == SortKind.ARRAY:
        default, entries = array_cells(sx)
        arr = tm.mk_const_array(sort, value_of(default, sort.range(), tm))
        for idx, el in entries:
            arr = tm.mk_term(Kind.STORE, [arr, value_of(idx, sort.domain(), tm), value_of(el, sort.range(), tm)])
        return arr
    raise ParseError("cannot read %s as a value of sort %r" % (write_sexpr(sx), sort), code=ErrorCode.PARSE)


def _bits(tok):
    if tok.startswith("#b"):
        return tok[2:]
    if tok.startswith("#x"):
        return "".join(format(int(c, 16), "04b") for c in tok[2:])
    raise ParseError("expected a bit-vector literal, got %s" % tok, code=ErrorCode.PARSE)


def _rational_of(sx):
    if isinstance(sx, str):
        try:
            return Fraction(sx)
        except (ValueError, ZeroDivisionError):
            return None
    if len(sx) == 2 and sx[0] == "-":
        f = _rational_of(sx[1])
        return None if f is None else -f
    if len(sx) == 3 and sx[0] == "/":
        a, b = _rational_of(sx[1]), _rational_of(sx[2])
        return None if a is None or b is None or b == 0 else a / b
    return None


def array_cells(sx):
    """(default, [(index, element), ...]) of a printed array value: a store chain over
    ((as const S) d). Outer stores win (the same index stored twice keeps the last)."""
    entries = []
    while isinstance(sx, list) and len(sx) == 4 and sx[0] == "store":
        entries.append((sx[2], sx[3]))
        sx = sx[1]
    if isinstance(sx, list) and len(sx) == 2 and isinstance(sx[0], list) and len(sx[0]) == 3 and sx[0][0] == "as" \
            and sx[0][1] == "const":
        default = sx[1]
    else:
        raise ParseError("expected a store chain over (as const ...), got %s" % write_sexpr(sx), code=ErrorCode.PARSE)
    entries.reverse()
    seen = {}
    for idx, el in entries:
        seen[write_sexpr(idx)] = (idx, el)
    return default, list(seen.values())


def uninterpreted_index(sx):
    """k of a printed uninterpreted value S!k; None if sx is not one."""
    if isinstance(sx, str):
        m = re.match(r"^.*!(\d+)$", unquote_symbol(sx))
        if m:
            return int(m.group(1))
    return None


# ---------------------------------------------------------------- terms as structure

_TAG_VALUE = 0
_TAG_SYMBOL = 1
_TAG_APP = 2
_TAG_TABLE = 3


def _sym_name(t):
    """The name of a declared (named) symbol, or None for an anonymous one."""
    name = t.symbol()
    if name is None:
        return None
    tm = t._manager()
    return name if tm.symbol(name) is t else None


def _encode_node(t, index_of):
    """One node of the encoding: a value, a symbol, or an application naming its children by
    their places in the table (`index_of`)."""
    from ._terms import SortKind
    if t.is_value():
        k = t.sort_kind()
        if k == SortKind.UNINTERPRETED:
            raise Unsupported("a value of an uninterpreted sort (%s) cannot be rebuilt in another manager"
                              % t.sexpr(), code=ErrorCode.UNSUPPORTED, function="encode_term")
        return (_TAG_VALUE, sort_text(t.sort()), t.sexpr())
    kind = Kind(t.kind())
    if kind == Kind.CONSTANT:
        if t.is_defined_function():
            raise Unsupported("a define-fun handle cannot be rebuilt as an uninterpreted declaration; "
                              "translate an application or export the solver with to_smt2()",
                              code=ErrorCode.UNSUPPORTED, function="encode_term")
        name = _sym_name(t)
        if name is None:
            raise Unsupported("the anonymous symbol %s (mk_fresh) is not in the name table and cannot be rebuilt "
                              "elsewhere; declare it by name instead" % t.sexpr(),
                              code=ErrorCode.UNSUPPORTED, function="encode_term")
        return (_TAG_SYMBOL, name, sort_text(t.sort()))
    children = tuple(index_of[c.id] for c in t.children())
    result_sort = sort_text(t.sort()) if kind == Kind.CONST_ARRAY else None
    return (_TAG_APP, int(kind), tuple(t.indices()), result_sort, children)


def encode_term(t):
    """The structural encoding of t (the pickle payload; rebuilt through the target manager's
    name table): a table of nodes -- kinds, indices, sort texts, values and symbol names --
    each after the nodes it names, the last one t. Flat, so neither building it nor pickling
    it recurses per level of the term, and a shared subterm is one entry."""
    index_of = {}
    table = []
    stack = [(t, False)]
    while stack:
        u, expanded = stack.pop()
        if u.id in index_of:
            continue
        leaf = u.is_value() or Kind(u.kind()) == Kind.CONSTANT
        if not expanded and not leaf:
            stack.append((u, True))
            for c in reversed(u.children()):  # popped left to right: symbols meet in order
                if c.id not in index_of:
                    stack.append((c, False))
            continue
        index_of[u.id] = len(table)
        table.append(_encode_node(u, index_of))
    return (_TAG_TABLE, tuple(table))


def decode_term(enc, tm):
    """t rebuilt in tm from encode_term's table."""
    if enc[0] != _TAG_TABLE:
        raise ValueError("not an encoded term")
    built = []
    for node in enc[1]:
        tag = node[0]
        if tag == _TAG_VALUE:
            built.append(value_of(read_sexpr(node[2]), parse_sort(node[1], tm), tm))
        elif tag == _TAG_SYMBOL:
            built.append(tm.declare(node[1], parse_sort(node[2], tm)))
        else:
            _, kind, indices, result_sort, children = node
            sort = parse_sort(result_sort, tm) if result_sort is not None else None
            built.append(tm.mk_term(Kind(kind), [built[i] for i in children], indices, sort))
    return built[-1]


def reduce_term(t):
    return (unpickle_term, (encode_term(t),))


def unpickle_term(enc):
    from ._terms import main_tm
    return decode_term(enc, main_tm())


def translate_term(t, tm):
    """Rebuild t in another manager through its name table (the same term when tm is t's)."""
    if tm is t._manager():
        return t
    return decode_term(encode_term(t), tm)


# ---------------------------------------------------------------- models from text


def parse_model_text(text):
    """[(name, kind, sort_sx, body_sx, formals)] from the printed SMT-LIB model: kind is
    'scalar', 'array' or 'function'; formals the (name, sort) list of a function."""
    exprs = read_all(text)
    if len(exprs) == 1 and isinstance(exprs[0], list) and exprs[0] and isinstance(exprs[0][0], list):
        exprs = exprs[0]  # the ( ... ) wrapper around the define-funs
    out = []
    for e in exprs:
        if not (isinstance(e, list) and len(e) == 5 and e[0] == "define-fun"):
            if isinstance(e, list) and e and e[0] == "model":
                out.extend(parse_model_text(write_sexpr(e[1:]) if len(e) > 1 else ""))
                continue
            raise ParseError("expected (define-fun name (args) sort body), got %s" % write_sexpr(e),
                             code=ErrorCode.PARSE)
        _, name, formals, sort_sx, body = e
        name = unquote_symbol(name)
        if formals:
            out.append((name, "function", sort_sx, body, [(unquote_symbol(f[0]), f[1]) for f in formals]))
        elif isinstance(sort_sx, list) and sort_sx and sort_sx[0] == "Array":
            out.append((name, "array", sort_sx, body, []))
        else:
            out.append((name, "scalar", sort_sx, body, []))
    return out


def function_cases(body, formals):
    """[(arg_sx tuple, value_sx)], else_sx of an (ite (and (= x!i c) ...) v else) chain."""
    cases = []
    names = [f[0] for f in formals]
    while isinstance(body, list) and len(body) == 4 and body[0] == "ite":
        guard, value, body = body[1], body[2], body[3]
        eqs = guard[1:] if isinstance(guard, list) and guard and guard[0] == "and" else [guard]
        args = [None] * len(names)
        for eq in eqs:
            if not (isinstance(eq, list) and len(eq) == 3 and eq[0] == "="):
                raise ParseError("unexpected guard %s in a function value" % write_sexpr(eq), code=ErrorCode.PARSE)
            lhs, rhs = unquote_symbol(eq[1]) if isinstance(eq[1], str) else None, eq[2]
            if lhs not in names:
                lhs, rhs = (unquote_symbol(eq[2]) if isinstance(eq[2], str) else None), eq[1]
            if lhs not in names:
                raise ParseError("unexpected guard %s in a function value" % write_sexpr(eq), code=ErrorCode.PARSE)
            args[names.index(lhs)] = rhs
        cases.append((tuple(args), value))
    return cases, body


def model_from_smt2(text, tm, solver_factory):
    """Rebuild a Model on tm from the text of Model.to_smt2(): the symbols are declared (or found)
    in tm's name table and a solver is asked for a model of the equalities that pin their
    values. Arrays are pinned cell by cell and functions case by case (their defaults come
    from the solver's own fill rule); values of uninterpreted sorts are pinned up to the
    equalities and disequalities among the symbols of each sort."""
    from ._terms import SortKind
    rows = parse_model_text(text)
    constraints = []
    by_sort = {}
    for name, kind, sort_sx, body, formals in rows:
        if kind == "function":
            fsort = tm.fun_sort([parse_sort(f[1], tm) for f in formals], parse_sort(sort_sx, tm))
            f = tm.declare(name, fsort)
            cases, _else = function_cases(body, formals)
            for args, value in cases:
                if any(a is None for a in args):
                    continue
                vargs = [value_of(a, fsort.domain(i), tm) for i, a in enumerate(args)]
                constraints.append(tm.mk_term(Kind.EQUAL, [tm.mk_term(Kind.APPLY, [f] + vargs),
                                                           value_of(value, fsort.range(), tm)]))
            continue
        sort = parse_sort(sort_sx, tm)
        sym = tm.declare(name, sort)
        if kind == "array":
            default, entries = array_cells(body)
            for idx, el in entries:
                constraints.append(tm.mk_term(Kind.EQUAL, [tm.mk_term(Kind.SELECT, [sym, value_of(idx, sort.domain(), tm)]),
                                                           value_of(el, sort.range(), tm)]))
            continue
        if sort.kind() == SortKind.UNINTERPRETED:
            k = uninterpreted_index(body)
            if k is None:
                raise ParseError("cannot read %s as a value of %r" % (write_sexpr(body), sort), code=ErrorCode.PARSE)
            by_sort.setdefault(sort, []).append((sym, k))
            continue
        constraints.append(tm.mk_term(Kind.EQUAL, [sym, value_of(body, sort, tm)]))
    for syms in by_sort.values():
        for i in range(len(syms)):
            for j in range(i + 1, len(syms)):
                (a, ka), (b, kb) = syms[i], syms[j]
                if ka == kb:
                    constraints.append(tm.mk_term(Kind.EQUAL, [a, b]))
                else:
                    constraints.append(tm.mk_term(Kind.DISTINCT, [a, b]))
    return solver_factory(tm, constraints)
