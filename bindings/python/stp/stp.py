"""
The MIT License

Copyright (c) 2008 Vijay Ganesh
              2014 Jurriaan Bremer, jurriaanbremer@gmail.com

Permission is hereby granted, free of charge, to any person obtaining
a copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be
included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
"""

import ast
from ctypes import cdll, POINTER, CFUNCTYPE
from ctypes import c_char_p, c_void_p, c_int32, c_uint32, c_uint64, c_ulong
import inspect
import os.path
import sys

__all__ = [
    'Expr', 'Solver', 'stp', 'add', 'bitvec', 'bitvecs', 'check', 'model',
]

Py3 = sys.version_info >= (3, 0, 0)

if Py3:
    long = int

from . library_path import PATHS

for path in PATHS:
    if not os.path.exists(path):
        continue

    _lib = cdll.LoadLibrary(path)
    break
else:
    raise Exception('Unable to locate the libstp shared object')


def _set_func(name, restype, *argtypes):
    getattr(_lib, name).restype = restype
    getattr(_lib, name).argtypes = argtypes

_VC = c_void_p
_Expr = c_void_p
_Type = c_void_p
_WholeCounterExample = c_void_p

_set_func('vc_createValidityChecker', _VC)
_set_func('vc_boolType', _Type, _VC)
_set_func('vc_arrayType', _Type, _VC, _Type, _Type)
_set_func('vc_varExpr', _Expr, _VC, c_char_p, _Type)
_set_func('vc_varExpr1', _Expr, _VC, c_char_p, c_int32, c_int32)
_set_func('vc_getType', _Type, _VC, _Expr)
_set_func('vc_getBVLength', c_int32, _VC, _Expr)
_set_func('vc_eqExpr', _Expr, _VC, _Expr, _Expr)
_set_func('vc_trueExpr', _Expr, _VC)
_set_func('vc_falseExpr', _Expr, _VC)
_set_func('vc_notExpr', _Expr, _VC, _Expr)
_set_func('vc_andExpr', _Expr, _VC, _Expr, _Expr)
_set_func('vc_andExprN', _Expr, _VC, POINTER(_Expr), c_int32)
_set_func('vc_orExpr', _Expr, _VC, _Expr, _Expr)
_set_func('vc_xorExpr', _Expr, _VC, _Expr, _Expr)
_set_func('vc_orExprN', _Expr, _VC, POINTER(_Expr), c_int32)
_set_func('vc_impliesExpr', _Expr, _VC, _Expr, _Expr)
_set_func('vc_iffExpr', _Expr, _VC, _Expr, _Expr)
_set_func('vc_iteExpr', _Expr, _VC, _Expr, _Expr, _Expr)
_set_func('vc_boolToBVExpr', _Expr, _VC, _Expr)
_set_func('vc_paramBoolExpr', _Expr, _VC, _Expr, _Expr)
_set_func('vc_readExpr', _Expr, _VC, _Expr, _Expr)
_set_func('vc_writeExpr', _Expr, _VC, _Expr, _Expr, _Expr)
_set_func('vc_parseExpr', _Expr, _VC, c_char_p)
_set_func('vc_printExpr', None, _VC, _Expr)
_set_func('vc_printExprCCode', None, _VC, _Expr)
_set_func('vc_printSMTLIB', c_char_p, _VC, _Expr)
_set_func('vc_printExprFile', None, _VC, _Expr, c_int32)
_set_func('vc_printExprToBuffer', None, _VC, _Expr, POINTER(c_char_p), POINTER(c_ulong))
_set_func('vc_printCounterExample', None, _VC)
_set_func('vc_printVarDecls', None, _VC)
_set_func('vc_clearDecls', None, _VC)
_set_func('vc_printAsserts', None, _VC, c_int32)
_set_func('vc_printQueryStateToBuffer', None, _VC, _Expr, POINTER(c_char_p), POINTER(c_ulong), c_int32)
_set_func('vc_printCounterExampleToBuffer', None, _VC, POINTER(c_char_p), POINTER(c_ulong))
_set_func('vc_printQuery', None, _VC)
_set_func('vc_assertFormula', None, _VC, _Expr)
_set_func('vc_simplify', _Expr, _VC, _Expr)
_set_func('vc_query_with_timeout', c_int32, _VC, _Expr, c_int32)
_set_func('vc_query', c_int32, _VC, _Expr)
_set_func('vc_getCounterExample', _Expr, _VC, _Expr)
_set_func('vc_getCounterExampleArray', None, _VC, _Expr, POINTER(POINTER(_Expr)), POINTER(POINTER(_Expr)), POINTER(c_int32))
_set_func('vc_counterexample_size', c_int32, _VC)
_set_func('vc_push', None, _VC)
_set_func('vc_pop', None, _VC)
_set_func('getBVInt', c_int32, _Expr)
_set_func('getBVUnsigned', c_uint32, _Expr)
_set_func('getBVUnsignedLongLong', c_uint64, _Expr)
_set_func('vc_bvType', _Type, _VC, c_int32)
_set_func('vc_bv32Type', _Type, _VC)
_set_func('vc_bvConstExprFromDecStr', _Expr, _VC, c_int32, c_char_p)
_set_func('vc_bvConstExprFromStr', _Expr, _VC, c_char_p)
_set_func('vc_bvConstExprFromInt', _Expr, _VC, c_int32, c_uint32)
_set_func('vc_bvConstExprFromLL', _Expr, _VC, c_int32, c_uint64)
_set_func('vc_bv32ConstExprFromInt', _Expr, _VC, c_uint32)
_set_func('vc_bvConcatExpr', _Expr, _VC, _Expr, _Expr)
_set_func('vc_bvPlusExpr', _Expr, _VC, c_int32, _Expr, _Expr)
_set_func('vc_bvPlusExprN', _Expr, _VC, c_int32, POINTER(_Expr), c_int32)
_set_func('vc_bv32PlusExpr', _Expr, _VC, _Expr, _Expr)
_set_func('vc_bvMinusExpr', _Expr, _VC, c_int32, _Expr, _Expr)
_set_func('vc_bv32MinusExpr', _Expr, _VC, _Expr, _Expr)
_set_func('vc_bvMultExpr', _Expr, _VC, c_int32, _Expr, _Expr)
_set_func('vc_bv32MultExpr', _Expr, _VC, _Expr, _Expr)
_set_func('vc_bvDivExpr', _Expr, _VC, c_int32, _Expr, _Expr)
_set_func('vc_bvModExpr', _Expr, _VC, c_int32, _Expr, _Expr)
_set_func('vc_sbvDivExpr', _Expr, _VC, c_int32, _Expr, _Expr)
_set_func('vc_sbvModExpr', _Expr, _VC, c_int32, _Expr, _Expr)
_set_func('vc_sbvRemExpr', _Expr, _VC, c_int32, _Expr, _Expr)
_set_func('vc_bvLtExpr', _Expr, _VC, _Expr, _Expr)
_set_func('vc_bvLeExpr', _Expr, _VC, _Expr, _Expr)
_set_func('vc_bvGtExpr', _Expr, _VC, _Expr, _Expr)
_set_func('vc_bvGeExpr', _Expr, _VC, _Expr, _Expr)
_set_func('vc_sbvLtExpr', _Expr, _VC, _Expr, _Expr)
_set_func('vc_sbvLeExpr', _Expr, _VC, _Expr, _Expr)
_set_func('vc_sbvGtExpr', _Expr, _VC, _Expr, _Expr)
_set_func('vc_sbvGeExpr', _Expr, _VC, _Expr, _Expr)
_set_func('vc_bvUMinusExpr', _Expr, _VC, _Expr)
_set_func('vc_bvAndExpr', _Expr, _VC, _Expr, _Expr)
_set_func('vc_bvOrExpr', _Expr, _VC, _Expr, _Expr)
_set_func('vc_bvXorExpr', _Expr, _VC, _Expr, _Expr)
_set_func('vc_bvNotExpr', _Expr, _VC, _Expr)
_set_func('vc_bvLeftShiftExprExpr', _Expr, _VC, c_int32, _Expr, _Expr)
_set_func('vc_bvRightShiftExprExpr', _Expr, _VC, c_int32,  _Expr, _Expr)
_set_func('vc_bvSignedRightShiftExprExpr', _Expr, _VC, c_int32, _Expr, _Expr)
_set_func('vc_bvLeftShiftExpr', _Expr, _VC, c_int32, _Expr)
_set_func('vc_bvRightShiftExpr', _Expr, _VC, c_int32, _Expr)
_set_func('vc_bv32LeftShiftExpr', _Expr, _VC, c_int32, _Expr)
_set_func('vc_bv32RightShiftExpr', _Expr, _VC, c_int32, _Expr)
_set_func('vc_bvVar32LeftShiftExpr', _Expr, _VC, _Expr, _Expr)
_set_func('vc_bvVar32RightShiftExpr', _Expr, _VC, _Expr, _Expr)
_set_func('vc_bvVar32DivByPowOfTwoExpr', _Expr, _VC, _Expr, _Expr)
_set_func('vc_bvExtract', _Expr, _VC, _Expr, c_int32, c_int32)
_set_func('vc_bvBoolExtract', _Expr, _VC, _Expr, c_int32)
_set_func('vc_bvBoolExtract_Zero', _Expr, _VC, _Expr, c_int32)
_set_func('vc_bvBoolExtract_One', _Expr, _VC, _Expr, c_int32)
_set_func('vc_bvSignExtend', _Expr, _VC, _Expr, c_int32)
_set_func('vc_bvCreateMemoryArray', _Expr, _VC, c_char_p)
_set_func('vc_bvReadMemoryArray', _Expr, _VC, _Expr, _Expr, c_int32)
_set_func('vc_bvWriteToMemoryArray', _Expr, _VC, _Expr, _Expr, _Expr, c_int32)
_set_func('vc_bv32ConstExprFromInt', _Expr, _VC, c_uint32)
_set_func('exprString', c_char_p, _Expr)
_set_func('typeString', c_char_p, _Type)
_set_func('getChild', _Expr, _Expr, c_int32)
_set_func('vc_isBool', c_int32, _Expr)
_set_func('vc_registerErrorHandler', None, CFUNCTYPE(None, c_char_p))
_set_func('vc_getHashQueryStateToBuffer', c_int32, _VC, _Expr)
_set_func('vc_Destroy', None, _VC)
_set_func('vc_DeleteExpr', None, _Expr)
_set_func('vc_getWholeCounterExample', _WholeCounterExample, _VC)
_set_func('vc_getTermFromCounterExample', _Expr, _VC, _Expr, _WholeCounterExample)
_set_func('vc_deleteWholeCounterExample', None, _WholeCounterExample)
_set_func('getDegree', c_int32, _Expr)
_set_func('getBVLength', c_int32, _Expr)
_set_func('getVWidth', c_int32, _Expr)
_set_func('getIWidth', c_int32, _Expr)
_set_func('vc_printCounterExampleFile', None, _VC, c_int32)
_set_func('exprName', c_char_p, _Expr)
_set_func('getExprID', c_int32, _Expr)
_set_func('vc_parseMemExpr', c_int32, _VC, c_char_p, POINTER(_Expr), POINTER(_Expr))


class Solver(object):
    current = None

    def __init__(self):
        self.keys = {}
        self.vc = _lib.vc_createValidityChecker()
        assert self.vc is not None, 'Error creating validity checker'

    def __del__(self):
        # TODO We're not quite there yet.
        # _lib.vc_Destroy(self.vc)
        pass

    def __enter__(self):
        Solver.current = self
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        Solver.current = None

    def bitvec(self, name, width=32):
        """Creates a new BitVector variable."""
        # TODO Sanitize the name or stp will segfault.
        # TODO Perhaps cache these calls per width?
        # TODO Please, please, fix this terrible Py3 support.
        name_conv = bytes(name, 'utf8') if Py3 else name

        bv_type = _lib.vc_bvType(self.vc, width)
        self.keys[name] = _lib.vc_varExpr(self.vc, name_conv, bv_type)
        return Expr(self, width, self.keys[name], name=name)

    def bitvecs(self, names, width=32):
        """Creates one or more BitVectors variables."""
        return [self.bitvec(name, width) for name in names.split()]

    def bitvecval(self, width, value):
        """Creates a new BitVector with a constant value."""
        expr = _lib.vc_bvConstExprFromLL(self.vc, width, value)
        return Expr(self, width, expr)

    def true(self):
        """Creates a True boolean."""
        return Expr(self, None, _lib.vc_trueExpr(self.vc))

    def false(self):
        """Creates a False boolean."""
        return Expr(self, None, _lib.vc_falseExpr(self.vc))

    def add(self, *exprs):
        """Adds one or more constraint(s) to STP."""
        for expr in exprs:
            assert isinstance(expr, Expr), 'Formula should be an Expression'
            _lib.vc_assertFormula(self.vc, expr.expr)

    def push(self):
        """Enter a new frame."""
        _lib.vc_push(self.vc)

    def pop(self):
        """Leave the current frame."""
        _lib.vc_pop(self.vc)

    def _n_exprs(self, *exprs):
        """Creates an array of Expressions to be used in the C API."""
        for expr in exprs:
            assert isinstance(expr, Expr), 'Object should be an Expression'

        # This may not be very clean, but I'm not sure if there are
        # better ways to achieve this goal.
        exprs = [expr.expr for expr in exprs]
        exprs = (_Expr * len(exprs))(*exprs)
        return exprs, len(exprs)

    def check(self, *exprs):
        """Check whether the various expressions are satisfiable."""

        _, length = self._n_exprs(*exprs)
        if (length > 0):
            expr = self.and_(*exprs)
            expr = _lib.vc_notExpr(self.vc, expr.expr)
        else:
            expr = self.false().expr

        _lib.vc_push(self.vc)
        ret = _lib.vc_query(self.vc, expr)
        _lib.vc_pop(self.vc)

        assert ret == 0 or ret == 1, 'Error querying your input'
        return not ret

    def model(self, key=None):
        """Returns a model for the entire Counter Example of BitVectors."""
        if key is not None:
            value = _lib.vc_getCounterExample(self.vc, self.keys[key])
            return _lib.getBVUnsignedLongLong(value)

        return dict((k, self.model(k)) for k in self.keys)

    # Allows easy access to the Counter Example.
    __getitem__ = model

    def and_(self, *exprs):
        exprs, length = self._n_exprs(*exprs)
        expr = _lib.vc_andExprN(self.vc, exprs, length)
        return Expr(self, None, expr)

    def or_(self, *exprs):
        exprs, length = self._n_exprs(*exprs)
        expr = _lib.vc_orExprN(self.vc, exprs, length)
        return Expr(self, None, expr)

    def xor(self, a, b):
        assert isinstance(a, Expr), 'Object must be an Expression'
        assert isinstance(b, Expr), 'Object must be an Expression'
        expr = _lib.vc_xorExpr(self.vc, a.expr, b.expr)
        return Expr(self, None, expr)

    def not_(self, obj):
        assert isinstance(obj, Expr), 'Object should be an Expression'
        expr = _lib.vc_notExpr(self.vc, obj.expr)
        return Expr(self, obj.width, expr)


class Expr(object):
    def __init__(self, s, width, expr, name=None):
        self.s = s
        self.width = width
        self.expr = expr
        self.name = name

    def __del__(self):
        # TODO We're not quite there yet.
        # _lib.vc_DeleteExpr(self.expr)
        pass

    def _1(self, cb):
        """Wrapper around single-expression STP functions."""
        expr = cb(self.s.vc, self.expr)
        return Expr(self.s, self.width, expr)

    def _1w(self, cb):
        """Wrapper around single-expression with width STP functions."""
        expr = cb(self.s.vc, self.width, self.expr)
        return Expr(self.s, self.width, expr)

    def _toexpr(self, other):
        if isinstance(other, (int, long)):
            return self.s.bitvecval(self.width, other)

        if isinstance(other, bool):
            return self.s.true() if other else self.s.false()

        return other

    def _2(self, cb, other):
        """Wrapper around double-expression STP functions."""
        other = self._toexpr(other)
        assert isinstance(other, Expr), \
            'Other object must be an Expr instance'
        expr = cb(self.s.vc, self.expr, other.expr)
        return Expr(self.s, self.width, expr)

    def _2w(self, cb, a, b):
        """Wrapper around double-expression with width STP functions."""
        a, b = self._toexpr(a), self._toexpr(b)
        assert isinstance(a, Expr), \
            'Left operand must be an Expr instance'
        assert isinstance(b, Expr), \
            'Right operand must be an Expr instance'
        assert self.width == a.width, 'Width must be equal'
        assert self.width == b.width, 'Width must be equal'
        expr = cb(self.s.vc, self.width, a.expr, b.expr)
        return Expr(self.s, self.width, expr)

    def add(self, other):
        return self._2w(_lib.vc_bvPlusExpr, self, other)

    __add__ = add
    __radd__ = add

    def sub(self, other):
        return self._2w(_lib.vc_bvMinusExpr, self, other)

    __sub__ = sub

    def rsub(self, other):
        return self._2w(_lib.vc_bvMinusExpr, other, self)

    __rsub__ = rsub

    def mul(self, other):
        return self._2w(_lib.vc_bvMultExpr, self, other)

    __mul__ = mul
    __rmul__ = mul

    def div(self, other):
        return self._2w(_lib.vc_bvDivExpr, self, other)

    __div__ = div
    __floordiv__ = div

    def rdiv(self, other):
        return self._2w(_lib.vc_bvDivExpr, other, self)

    __rdiv__ = rdiv
    __rfloordiv__ = rdiv

    def mod(self, other):
        return self._2w(_lib.vc_bvModExpr, self, other)

    __mod__ = mod

    def rmod(self, other):
        return self._2w(_lib.vc_bvModExpr, other, self)

    __rmod__ = rmod

    def rem(self, other):
        return self._2w(_lib.vc_bvRemExpr, self, other)

    def rrem(self, other):
        return self._2w(_lib.vc_bvRemExpr, other, self)

    def sdiv(self, other):
        return self._2w(_lib.vc_sbvDivExpr, self, other)

    def rsdiv(self, other):
        return self._2w(_lib.vc_sbvDivExpr, other, self)

    def smod(self, other):
        return self._2w(_lib.vc_sbvModExpr, self, other)

    def rsmod(self, other):
        return self._2w(_lib.vc_sbvModExpr, other, self)

    def srem(self, other):
        return self._2w(_lib.vc_sbvRemExpr, self, other)

    def rsrem(self, other):
        return self._2w(_lib.vc_sbvRemExpr, other, self)

    def eq(self, other):
        return self._2(_lib.vc_eqExpr, other)

    __eq__ = eq

    def ne(self, other):
        return self.s.not_(self.eq(other))

    __ne__ = ne

    def lt(self, other):
        return self._2(_lib.vc_bvLtExpr, other)

    __lt__ = lt

    def le(self, other):
        return self._2(_lib.vc_bvLeExpr, other)

    __le__ = le

    def gt(self, other):
        return self._2(_lib.vc_bvGtExpr, other)

    __gt__ = gt

    def ge(self, other):
        return self._2(_lib.vc_bvGeExpr, other)

    __ge__ = ge

    def slt(self, other):
        return self._2(_lib.vc_sbvLtExpr, other)

    def sle(self, other):
        return self._2(_lib.vc_sbvLeExpr, other)

    def sgt(self, other):
        return self._2(_lib.vc_sbvGtExpr, other)

    def sge(self, other):
        return self._2(_lib.vc_sbvGeExpr, other)

    def and_(self, other):
        return self._2(_lib.vc_bvAndExpr, other)

    __and__ = and_
    __rand__ = and_

    def or_(self, other):
        return self._2(_lib.vc_bvOrExpr, other)

    __or__ = or_
    __ror__ = or_

    def xor(self, other):
        return self._2(_lib.vc_bvXorExpr, other)

    __xor__ = xor
    __rxor__ = xor

    def neg(self):
        return self._1(_lib.vc_bvUMinusExpr)

    __neg__ = neg

    def __pos__(self):
        return self

    def not_(self):
        return self._1(_lib.vc_bvNotExpr)

    __invert__ = not_

    def shl(self, other):
        return self._2w(_lib.vc_bvLeftShiftExprExpr, self, other)

    __lshift__ = shl

    def rshl(self, other):
        return self._2w(_lib.vc_bvLeftShiftExprExpr, other, self)

    __rlshift__ = rshl

    def shr(self, other):
        return self._2w(_lib.vc_bvRightShiftExprExpr, self, other)

    __rshift__ = shr

    def rshr(self, other):
        return self._2w(_lib.vc_bvRightShiftExprExpr, other, self)

    __rrshift__ = rshr

    def sar(self, other):
        return self._2w(_lib.vc_bvSignedRightShiftExprExpr, self, other)

    def rsar(self, other):
        return self._2w(_lib.vc_bvSignedRightShiftExprExpr, other, self)

    def extract(self, high, low):
        expr = _lib.vc_bvExtract(self.s.vc, self.expr, high, low)
        return Expr(self.s, self.width, expr)

    def simplify(self):
        """Simplify an expression."""
        expr = _lib.vc_simplify(self.s.vc, self.expr)
        return Expr(self.s, self.width, expr)

    @property
    def value(self):
        """Returns the value of this BitVec in the current model."""
        return self.s.model(self.name)


class ASTtoSTP(ast.NodeVisitor):
    def __init__(self, s, count, *args, **kwargs):
        ast.NodeVisitor.__init__(self)
        self.s = s
        self.count = count
        self.inside = False
        self.func_name = None
        self.bitvecs = {}
        self.exprs = []
        self.returned = None
        self.args = args
        self.kwargs = kwargs

    def _super(self, node):
        return super(ASTtoSTP, self).generic_visit(node)

    visit_Module = _super

    def visit_FunctionDef(self, node):
        assert node.args.vararg is None and node.args.kwarg is None, \
            'Variable and Keyword arguments are not allowed'

        if self.inside:
            raise Exception('Nested functions are not allowed')

        self.inside = True
        self.func_name = node.name

        for idx, arg in enumerate(node.args.args):
            arg = arg.arg if Py3 else arg.id
            name = '%s_%d_%s' % (self.func_name, self.count, arg)
            if idx < len(self.args):
                self.bitvecs[name] = self.args[idx]
                continue

            if arg in self.kwargs:
                self.bitvecs[name] = self.kwargs[arg]
                continue

            width = 32
            if idx < len(node.args.defaults):
                width = node.args.defaults[idx]

            self.bitvecs[name] = self.s.bitvec(name, width=width)

        for row in node.body:
            self.visit(row)

    def visit_Num(self, node):
        return node.n

    def visit_BoolOp(self, node):
        ops = {
            ast.And: self.s.and_,
            ast.Or: self.s.or_,
        }
        x = self.visit(node.values[0])
        y = self.visit(node.values[1])
        return ops[node.op.__class__](x, y)

    def visit_BinOp(self, node):
        ops = {
            ast.Add: lambda x, y: x + y,
            ast.Sub: lambda x, y: x - y,
            ast.Mult: lambda x, y: x * y,
            ast.Div: lambda x, y: x / y,
            ast.Mod: lambda x, y: x % y,
            ast.LShift: lambda x, y: x << y,
            ast.RShift: lambda x, y: x >> y,
            ast.BitOr: lambda x, y: x | y,
            ast.BitXor: lambda x, y: x ^ y,
            ast.BitAnd: lambda x, y: x & y,
        }
        x = self.visit(node.left)
        y = self.visit(node.right)
        return ops[node.op.__class__](x, y)

    def visit_Compare(self, node):
        assert len(node.ops) == 1, 'TODO Support multiple comparison ops'

        cmps = {
            ast.Eq: lambda x, y: x == y,
            ast.NotEq: lambda x, y: x != y,
            ast.Lt: lambda x, y: x < y,
            ast.LtE: lambda x, y: x <= y,
            ast.Gt: lambda x, y: x > y,
            ast.GtE: lambda x, y: x >= y,
            ast.Is: lambda x, y: x == y,
            ast.IsNot: lambda x, y: x != y,
        }

        x = self.visit(node.left)
        y = self.visit(node.comparators[0])
        return cmps[node.ops[0].__class__](x, y)

    def visit_Name(self, node):
        if isinstance(node.ctx, ast.Load):
            name = '%s_%d_%s' % (self.func_name, self.count, node.id)
            return self.bitvecs[name]

        raise

    def visit_Assert(self, node):
        self.exprs.append(self.visit(node.test))

    def visit_Return(self, node):
        self.returned = self.visit(node.value)

    def generic_visit(self, node):
        raise Exception(node.__class__.__name__ + ' is not yet supported!')


def _eval_ast(root, *args, **kwargs):
    s = Solver.current
    node = ASTtoSTP(s, root.count-1, *args, **kwargs)
    node.visit(root)
    if node.exprs:
        s.add(*node.exprs)
    return node.returned


def stp(f):
    try:
        src = inspect.getsource(f)
    except IOError:
        raise Exception(
            'It is only possible to use the @stp decorator when the '
            'function is stored in a source file. It does *not* work '
            'directly from the Python interpreter.')

    node = ast.parse(src)
    node.count = 0

    def h(*args, **kwargs):
        node.count += 1
        return _eval_ast(node, *args, **kwargs)

    return h


def add(*args, **kwargs):
    return Solver.current.add(*args, **kwargs)


def bitvec(*args, **kwargs):
    return Solver.current.bitvec(*args, **kwargs)


def bitvecs(*args, **kwargs):
    return Solver.current.bitvecs(*args, **kwargs)


def check(*args, **kwargs):
    return Solver.current.check(*args, **kwargs)


def model(*args, **kwargs):
    return Solver.current.model(*args, **kwargs)
