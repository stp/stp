from ctypes import cdll, POINTER, CFUNCTYPE
from ctypes import c_char_p, c_void_p, c_int32, c_uint32, c_uint64, c_ulong
import os.path

PATHS = [
    './libstp.so',
]

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
    def __init__(self):
        self.keys = {}
        self.vc = _lib.vc_createValidityChecker()
        assert self.vc is not None, 'Error creating validity checker'

    def __del__(self):
        # TODO We're not quite there yet.
        # _lib.vc_Destroy(self.vc)
        pass

    def bitvec(self, name, width=32):
        """Creates a new BitVector variable."""
        # TODO Sanitize the name or stp will segfault.
        # TODO Perhaps cache these calls per width?
        bv_type = _lib.vc_bvType(self.vc, width)
        self.keys[name] = _lib.vc_varExpr(self.vc, name, bv_type)
        return Expr(self, width, self.keys[name], name=name)

    def bitvecs(self, names, width=32):
        """Creates one or more BitVectors variables."""
        return [self.bitvec(name, width) for name in names.split()]

    def bitvecval(self, width, value):
        """Creates a new BitVector with a constant value."""
        expr = _lib.vc_bvConstExprFromLL(self.vc, width, value)
        return Expr(self, width, expr)

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
        expr = self.and_(*exprs)
        expr = _lib.vc_notExpr(self.vc, expr.expr)
        ret = _lib.vc_query(self.vc, expr)
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
        return Expr(self.vc, None, expr)

    def or_(self, *exprs):
        exprs, length = self._n_exprs(*exprs)
        expr = _lib.vc_orExprN(self.vc, exprs, length)
        return Expr(self.vc, None, expr)

    def xor(self, a, b):
        assert isinstance(a, Expr), 'Object must be an Expression'
        assert isinstance(b, Expr), 'Object must be an Expression'
        expr = _lib.vc_xorExpr(self.vc, a.expr, b.expr)
        return Expr(self.vc, None, expr)

    def not_(self, obj):
        assert isinstance(obj, Expr), 'Object should be an Expression'
        expr = _lib.vc_notExpr(self.vc, obj.expr)
        return Expr(self.vc, obj.width, expr)


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

    def _2(self, cb, other):
        """Wrapper around double-expression STP functions."""
        if isinstance(other, (int, long)):
            other = self.s.bitvecval(self.width, other)

        assert isinstance(other, Expr), \
            'Other object must be an Expr instance'
        expr = cb(self.s.vc, self.expr, other.expr)
        return Expr(self.s, self.width, expr)

    def _2w(self, cb, other):
        """Wrapper around double-expression with width STP functions."""
        if isinstance(other, (int, long)):
            other = self.s.bitvecval(self.width, other)

        assert isinstance(other, Expr), \
            'Other object must be an Expr instance'
        assert self.width == other.width, 'Width must be equal'
        expr = cb(self.s.vc, self.width, self.expr, other.expr)
        return Expr(self.s, self.width, expr)

    def add(self, other):
        return self._2w(_lib.vc_bvPlusExpr, other)

    __add__ = add

    def sub(self, other):
        return self._2w(_lib.vc_bvMinusExpr, other)

    __sub__ = sub

    def mul(self, other):
        return self._2w(_lib.vc_bvMultExpr, other)

    __mul__ = mul

    def div(self, other):
        return self._2w(_lib.vc_bvDivExpr, other)

    __div__ = div

    def mod(self, other):
        return self._2w(_lib.vc_bvModExpr, other)

    __mod__ = mod

    def rem(self, other):
        return self._2w(_lib.vc_bvRemExpr, other)

    def sdiv(self, other):
        return self._2w(_lib.vc_sbvDivExpr, other)

    def smod(self, other):
        return self._2w(_lib.vc_sbvModExpr, other)

    def srem(self, other):
        return self._2w(_lib.vc_sbvRemExpr, other)

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

    def or_(self, other):
        return self._2(_lib.vc_bvOrExpr, other)

    __or__ = or_

    def xor(self, other):
        return self._2(_lib.vc_bvXorExpr, other)

    __xor__ = xor

    def not_(self):
        return self._1(_lib.vc_bvNotExpr)

    __invert__ = not_

    def shl(self, other):
        return self._2w(_lib.vc_bvLeftShiftExprExpr, other)

    __lshift__ = shl

    def shr(self, other):
        return self._2w(_lib.vc_bvRightShiftExprExpr, other)

    __rshift__ = shr

    def sar(self, other):
        return self._2w(_lib.vc_bvSignedRightShiftExprExpr, other)

    def extract(self, high, low):
        expr = _lib.vc_bvExtract(self.s.vc, self.expr, high, low)
        return Expr(self.s, self.width, expr)

    def simplify(self):
        """Simplify an expression."""
        expr = _lib.vc_simplify(self.s.vc, self.expr)
        return Expr(self.s, self.width, expr)
