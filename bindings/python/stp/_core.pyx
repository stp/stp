# cython: language_level=3, binding=True, embedsignature=True
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

"""stp._core -- the Cython layer of the STP 3.x Python API.

Thin wrappers that own the C handles of <stp/stp.h>: a Manager (stp_tm), Sort,
Term, OptionsHandle, SolverHandle, ModelHandle, ArrayValueHandle,
FunValueHandle and StatisticsHandle. Every failing C call is turned into the
stp.Error subclass its error code maps to (the manager's record is read and
cleared; a failed mutation also leaves the solver's failed state, because a
raised exception cannot be ignored). The GIL is released around the checks and
the parsers so that Solver.interrupt() works from another thread, and a wrapper
finalised off the manager's thread (or while a check runs) defers its release
to the manager's next entry point. The z3py-style surface (ExprRef, BitVec,
Solver, Model, ...) is built over these classes in stp/_terms.py and
stp/_solver.py; they register their classes here so that every wrapper the
core hands out is already of the right Python class.
"""

from libc.stdint cimport uint8_t, uint32_t, uint64_t, int64_t, UINT64_MAX, INT64_MIN
from libc.stdlib cimport malloc, free
from libc.string cimport memcpy, strlen
from libc.signal cimport signal, sighandler_t, SIGINT, SIG_ERR
from cpython.bytes cimport PyBytes_FromStringAndSize
from cpython.exc cimport PyErr_CheckSignals, PyErr_SetInterrupt

cdef extern from "pythread.h":
    unsigned long PyThread_get_thread_ident()

# The SIGINT bridge: while a check runs on the main thread, a C handler turns
# Ctrl-C into stp_solver_interrupt (async-signal-safe); afterwards the Python
# handler is restored and the interrupt is re-delivered to it, so the usual
# KeyboardInterrupt surfaces from check() and the solver stays usable.
cdef extern from *:
    """
    #include <signal.h>
    #include <stp/stp.h>
    static volatile sig_atomic_t stp_py_sigint_fired = 0;
    static stp_solver stp_py_sigint_target = NULL;
    static void stp_py_sigint_handler(int signum)
    {
      (void)signum;
      stp_py_sigint_fired = 1;
      if (stp_py_sigint_target != NULL)
        stp_solver_interrupt(stp_py_sigint_target);
    }
    """
    int stp_py_sigint_fired
    stp_solver stp_py_sigint_target
    void stp_py_sigint_handler(int) noexcept nogil

import re
import sys
import threading
import traceback
import weakref

from stp._gen_kinds import ErrorCode

# ----------------------------------------------------------------- errors

class Error(Exception):
    """The base of every STP exception.

    Attributes: code (ErrorCode), recoverable, function (the C API function
    that refused), argument_index (0-based or None), option (the option name
    for the OPTION_* codes) and terms (the terms involved, when known)."""
    code = None
    recoverable = True
    function = ""
    argument_index = None
    option = None
    terms = ()

    def __init__(self, message="", **fields):
        Exception.__init__(self, message)
        self.message = message
        for k, v in fields.items():
            setattr(self, k, v)

    def __str__(self):
        return self.message


class ArgumentError(Error, ValueError):
    """INVALID_ARGUMENT, ARITY, INDEX_OUT_OF_RANGE, VALUE_OUT_OF_RANGE, NULL_HANDLE."""


class SortMismatch(ArgumentError, TypeError):
    """SORT_MISMATCH and FOREIGN_MANAGER."""


class DoesNotFit(Error, OverflowError):
    """DOES_NOT_FIT: the value needs a wider native type; use the string, limb or bytes reader."""


class NotAValue(Error, TypeError):
    """NOT_A_VALUE: a reader was applied to a term that is not a value."""


class NoModel(Error):
    """NO_MODEL: the last check did not answer sat."""


class Unsupported(Error, NotImplementedError):
    """UNSUPPORTED by this build or engine."""


class OptionError(Error, ValueError):
    """OPTION_VALUE, OPTION_TIMING, OPTION_CONFLICT, OPTION_UNAVAILABLE."""


class UnknownOption(OptionError, KeyError):
    """OPTION_UNKNOWN."""

    def __str__(self):
        return self.message


class ParseError(Error, ValueError):
    """PARSE, with .lineno/.offset (aliases .line/.column)."""
    lineno = 0
    offset = 0

    @property
    def line(self):
        return self.lineno

    @property
    def column(self):
        return self.offset


class IOError(Error, OSError):
    """IO."""


class StateError(Error, RuntimeError):
    """STATE: pop below level 0, a closed solver, a poisoned object, a pinned manager used off its thread."""


class ResourceError(Error, MemoryError):
    """RESOURCE: the object is poisoned."""


class InternalError(Error):
    """INTERNAL: a violated invariant; the object is poisoned."""


_CLASS_BY_CODE = {
    STP_ERR_INVALID_ARGUMENT: ArgumentError,
    STP_ERR_SORT_MISMATCH: SortMismatch,
    STP_ERR_ARITY: ArgumentError,
    STP_ERR_INDEX_OUT_OF_RANGE: ArgumentError,
    STP_ERR_VALUE_OUT_OF_RANGE: ArgumentError,
    STP_ERR_DOES_NOT_FIT: DoesNotFit,
    STP_ERR_NOT_A_VALUE: NotAValue,
    STP_ERR_NO_MODEL: NoModel,
    STP_ERR_FOREIGN_MANAGER: SortMismatch,
    STP_ERR_NULL_HANDLE: ArgumentError,
    STP_ERR_UNSUPPORTED: Unsupported,
    STP_ERR_OPTION_UNKNOWN: UnknownOption,
    STP_ERR_OPTION_VALUE: OptionError,
    STP_ERR_OPTION_TIMING: OptionError,
    STP_ERR_OPTION_CONFLICT: OptionError,
    STP_ERR_OPTION_UNAVAILABLE: OptionError,
    STP_ERR_PARSE: ParseError,
    STP_ERR_IO: IOError,
    STP_ERR_STATE: StateError,
    STP_ERR_RESOURCE: ResourceError,
    STP_ERR_INTERNAL: InternalError,
}

_PARSE_POS = re.compile(r"parse error at (\d+):(\d+)")


cdef inline object _s(const char* p):
    """A C string as str; None for NULL."""
    if p == NULL:
        return None
    return (<bytes>p).decode("utf-8", "replace")


cdef inline object _take(char* p):
    """A caller-owned C string as str, freed; None for NULL."""
    if p == NULL:
        return None
    try:
        return (<bytes>p).decode("utf-8", "replace")
    finally:
        stp_free(p)


# Every live Manager by manager id: a call can hand back another manager's
# term (a FOREIGN_MANAGER error names it), and the term is that manager's.
_MANAGERS = weakref.WeakValueDictionary()


cdef Manager _manager_of(stp_term t, Manager m):
    """The Manager of the manager `t` belongs to; `m` for its own terms."""
    cdef stp_tm tm = stp_term_manager(t)  # +1
    cdef Manager owner
    if tm == NULL:
        return m
    try:
        if stp_tm_id(tm) == stp_tm_id(m._tm):
            return m
        owner = _MANAGERS.get(stp_tm_id(tm))
        if owner is None:
            # every wrapper of it is gone: a new one takes the reference
            owner = type(m).__new__(type(m))
            owner._tm = tm
            tm = NULL
            _MANAGERS[stp_tm_id(owner._tm)] = owner
        return owner
    finally:
        if tm != NULL:
            stp_tm_release(tm)


cdef object _exc_from(const stp_error* e, Manager m, bint with_terms):
    cls = _CLASS_BY_CODE.get(<int>e.code, InternalError)
    msg = _s(e.message) or _s(stp_error_code_name(e.code)) or "error"
    exc = cls(msg)
    try:
        exc.code = ErrorCode(<int>e.code)
    except ValueError:
        exc.code = <int>e.code
    exc.recoverable = bool(e.recoverable)
    exc.function = _s(e.function) or ""
    exc.argument_index = None if e.argument_index < 0 else e.argument_index
    exc.option = _s(e.option)
    cdef size_t i, n
    cdef stp_term t
    if with_terms and m is not None:
        n = stp_tm_error_num_terms(m._tm)
        ts = []
        for i in range(n):
            t = stp_tm_error_term(m._tm, i)
            if t != NULL:
                ts.append(_manager_of(t, m)._wrap(t))
        exc.terms = tuple(ts)
    if cls is ParseError:
        mo = _PARSE_POS.search(msg)
        if mo is not None:
            exc.lineno = int(mo.group(1))
            exc.offset = int(mo.group(2))
    return exc


cdef int _raise_thread_local(const char* fn) except -1:
    """Raise from the thread-local record (calls with no object to record into)."""
    cdef const stp_error* e = stp_last_error()
    if e == NULL:
        raise InternalError("'%s' failed without recording an error" % _s(fn))
    raise _exc_from(e, None, False)


# ----------------------------------------------------------------- deferred release
#
# Node reference counts are plain, and a manager is used by one thread at a
# time: the GIL serialises every wrapper finaliser with every other Python
# use of the manager, except while a check or a parse runs with the GIL
# released (Manager.busy). A wrapper finalised then, or after the cyclic
# garbage collector cleared its manager reference, must not touch the
# counts: its handle goes onto this queue, tagged with its manager, and the
# next entry point of any manager (on whichever thread) releases every queued
# handle whose manager is not busy then -- with the GIL held and the manager
# idle, nothing else can be touching its counts. A manager's own handle is
# tagged 0 and is never busy.

cdef enum:
    DEFER_TERM = 0
    DEFER_MODEL = 1
    DEFER_ARRAY = 2
    DEFER_FUN = 3
    DEFER_STATS = 4
    DEFER_SOLVER = 5
    DEFER_TM = 6
    DEFER_BOX = 7

_deferred = []
_deferred_lock = threading.Lock()
_busy_keys = set()  # the managers inside a check or a parse (the GIL is released there)


cdef void _set_busy(Manager m, bint flag):
    m._busy = flag
    with _deferred_lock:
        if flag:
            _busy_keys.add(<size_t>m._tm)
        else:
            _busy_keys.discard(<size_t>m._tm)


cdef void _defer(size_t key, int kind, void* h):
    try:
        with _deferred_lock:
            _deferred.append((key, kind, <size_t>h))
    except BaseException:
        pass  # a wrapper dying during interpreter teardown: leak rather than raise


cdef void _release_kind(int kind, void* h):
    if kind == DEFER_TERM:
        stp_term_release(<stp_term>h)
    elif kind == DEFER_MODEL:
        stp_model_release(<stp_model>h)
    elif kind == DEFER_ARRAY:
        stp_array_value_release(<stp_array_value>h)
    elif kind == DEFER_FUN:
        stp_fun_value_release(<stp_fun_value>h)
    elif kind == DEFER_STATS:
        stp_statistics_release(<stp_statistics>h)
    elif kind == DEFER_SOLVER:
        stp_solver_delete(<stp_solver>h)
    elif kind == DEFER_TM:
        stp_tm_release(<stp_tm>h)
    elif kind == DEFER_BOX:
        free(h)


cdef void _drain_idle():
    cdef list mine = []
    cdef list keep = []
    with _deferred_lock:
        for entry in _deferred:
            if entry[0] in _busy_keys:
                keep.append(entry)
            else:
                mine.append(entry)
        _deferred[:] = keep
    for entry in mine:
        _release_kind(<int>entry[1], <void*><size_t>entry[2])


def pending_releases():
    """The number of handles waiting on the deferred-release queue (for tests)."""
    with _deferred_lock:
        return len(_deferred)


def drain_releases():
    """Release every queued handle whose manager is not busy (also done at every entry point)."""
    _drain_idle()


# ----------------------------------------------------------------- class registration
#
# The pure-Python shell registers the classes the core instantiates: one per
# sort kind for terms (plain and value), one per sort kind for sorts, and the
# Model / ArrayValue / FunValue / Statistics classes.

cdef list _TERM_CLASSES = [[None, None] for _ in range(8)]
cdef list _SORT_CLASSES = [None] * 8
cdef object _MODEL_CLASS = None
cdef object _ARRAY_VALUE_CLASS = None
cdef object _FUN_VALUE_CLASS = None
cdef object _STATS_CLASS = None


def register_term_classes(mapping):
    """mapping: {sort_kind(int): (term_class, value_class)}; both subclasses of Term."""
    for k, (cls, vcls) in mapping.items():
        if not (issubclass(cls, Term) and issubclass(vcls, Term)):
            raise TypeError("term classes must subclass stp._core.Term")
        _TERM_CLASSES[int(k)][0] = cls
        _TERM_CLASSES[int(k)][1] = vcls


def register_sort_classes(mapping):
    """mapping: {sort_kind(int): sort_class}; subclasses of Sort."""
    for k, cls in mapping.items():
        if not issubclass(cls, Sort):
            raise TypeError("sort classes must subclass stp._core.Sort")
        _SORT_CLASSES[int(k)] = cls


def register_value_classes(model=None, array_value=None, fun_value=None, statistics=None):
    global _MODEL_CLASS, _ARRAY_VALUE_CLASS, _FUN_VALUE_CLASS, _STATS_CLASS
    if model is not None:
        if not issubclass(model, ModelHandle):
            raise TypeError("the model class must subclass stp._core.ModelHandle")
        _MODEL_CLASS = model
    if array_value is not None:
        if not issubclass(array_value, ArrayValueHandle):
            raise TypeError("the array value class must subclass stp._core.ArrayValueHandle")
        _ARRAY_VALUE_CLASS = array_value
    if fun_value is not None:
        if not issubclass(fun_value, FunValueHandle):
            raise TypeError("the function value class must subclass stp._core.FunValueHandle")
        _FUN_VALUE_CLASS = fun_value
    if statistics is not None:
        if not issubclass(statistics, StatisticsHandle):
            raise TypeError("the statistics class must subclass stp._core.StatisticsHandle")
        _STATS_CLASS = statistics


# ----------------------------------------------------------------- helpers

cdef inline bytes _b(object s):
    """A str (or bytes) as UTF-8 bytes for a const char* argument."""
    if isinstance(s, bytes):
        return <bytes>s
    if isinstance(s, str):
        return (<str>s).encode("utf-8")
    raise TypeError("expected a str, got %s" % type(s).__name__)


cdef object _int_from_hex(str digits, bint signed, uint32_t width):
    cdef object w = int(width)  # Python ints: a C shift by >= 64 is undefined
    v = int(digits, 16) if digits else 0
    if signed and w > 0 and v >= (1 << (w - 1)):
        v -= 1 << w
    return v


# ----------------------------------------------------------------- Manager

cdef class Manager:
    """A term manager (stp_tm): the node factory, the sort pool and the name table.

    Usable from any thread, one call at a time: the GIL serialises the Python
    entry points, and a check or a parse (which release it) must not overlap
    another call on the same manager. Solver.interrupt() may be called from
    any thread at any time. Any number of solvers may be live over one manager."""

    def __cinit__(self, *args, **kwargs):
        self._tm = NULL
        self._owner = PyThread_get_thread_ident()
        self._busy = False
        self._live = weakref.WeakValueDictionary()
        self._sorts = {}

    def __init__(self, OptionsHandle options=None, simplify=True, int default_rounding_mode=0,
                 uf_sort_width=16):
        """With `options`, the manager-scoped entries are read from it (a set
        solver-scoped entry is an OptionError); otherwise the three arguments
        are the manager entries."""
        if self._tm != NULL:
            raise StateError("Manager.__init__ called twice")
        if options is not None:
            self._tm = stp_tm_new(options._o)
        else:
            if default_rounding_mode < 0 or default_rounding_mode > <int>STP_RM_RTZ:
                raise ArgumentError("invalid rounding mode %d" % default_rounding_mode)
            self._tm = stp_tm_new_with(bool(simplify), <stp_rm>default_rounding_mode, <uint32_t>uf_sort_width)
        if self._tm == NULL:
            _raise_thread_local("stp_tm_new")
        _MANAGERS[stp_tm_id(self._tm)] = self

    def __dealloc__(self):
        if self._tm != NULL:
            if not self._busy:
                stp_tm_release(self._tm)
            else:
                _defer(0, DEFER_TM, <void*>self._tm)
            self._tm = NULL

    cdef int _check(self) except -1:
        if self._tm == NULL:
            raise StateError("the term manager is not initialised")
        if _deferred:
            _drain_idle()
        return 0

    cdef int _fail(self, const char* fn) except -1:
        cdef const stp_error* e = stp_tm_error(self._tm)
        cdef object exc
        if e == NULL:
            raise InternalError("'%s' failed without recording an error" % _s(fn))
        exc = _exc_from(e, self, True)
        stp_tm_clear_error(self._tm)
        raise exc

    cdef object _wrap(self, stp_term h):
        """Take ownership of the +1 reference `h` and return the (unique) wrapper for its node."""
        cdef uint64_t tid = stp_term_id(h)
        cdef object obj = self._live.get(tid)
        cdef stp_sort s
        cdef stp_sort_kind sk = STP_SORT_BOOL
        cdef Term term
        if obj is not None:
            stp_term_release(h)  # the wrapper already holds one
            return obj
        s = stp_term_sort(h)
        if s != NULL:
            stp_sort_get_kind(s, &sk)
        cls = _TERM_CLASSES[<int>sk][1 if stp_term_is_value(h) else 0]
        if cls is None:
            cls = Term
        obj = cls.__new__(cls)
        term = <Term>obj
        term._h = h
        term._m = self
        term._key = <size_t>self._tm
        self._live[tid] = obj
        return obj

    cdef object _wrap_sort(self, stp_sort h):
        cdef uint64_t sid = stp_sort_id(h)
        cdef object obj = self._sorts.get(sid)
        cdef stp_sort_kind sk = STP_SORT_BOOL
        cdef Sort sort
        if obj is not None:
            return obj
        stp_sort_get_kind(h, &sk)
        cls = _SORT_CLASSES[<int>sk]
        if cls is None:
            cls = Sort
        obj = cls.__new__(cls)
        sort = <Sort>obj
        sort._h = h
        sort._m = self
        self._sorts[sid] = obj
        return obj

    cdef stp_term* _array(self, list terms, size_t* n, const char* fn) except NULL:
        """A malloc'd stp_term[] of the handles of `terms` (all Terms of this manager)."""
        cdef size_t count = len(terms)
        cdef size_t i
        cdef stp_term* arr = <stp_term*>malloc((count if count > 0 else 1) * sizeof(stp_term))
        if arr == NULL:
            raise MemoryError()
        for i in range(count):
            obj = terms[i]
            if not isinstance(obj, Term):
                free(arr)
                raise TypeError("%s: argument %d is not a term (got %s)" % (_s(fn), i, type(obj).__name__))
            if (<Term>obj)._m is not self:
                free(arr)
                raise SortMismatch("%s: argument %d belongs to another term manager" % (_s(fn), i),
                                   code=ErrorCode.FOREIGN_MANAGER, function=_s(fn), argument_index=i)
            arr[i] = (<Term>obj)._h
        n[0] = count
        return arr

    cdef object _mk(self, stp_kind kind, list args, tuple indices, Sort sort, const char* fn):
        cdef size_t n = 0, m = len(indices), i
        cdef stp_term* arr = self._array(args, &n, fn)
        cdef uint32_t* idx = NULL
        cdef stp_term h
        try:
            if m > 0:
                idx = <uint32_t*>malloc(m * sizeof(uint32_t))
                if idx == NULL:
                    raise MemoryError()
                for i in range(m):
                    idx[i] = <uint32_t>indices[i]
            h = stp_mk_term_sorted(self._tm, kind, n, arr, m, idx, sort._h if sort is not None else NULL)
        finally:
            free(arr)
            free(idx)
        if h == NULL:
            self._fail(fn)
        return self._wrap(h)

    # ------------------------------------------------------------ identity and settings
    @property
    def id(self):
        return stp_tm_id(self._tm)

    @property
    def simplify(self):
        return bool(stp_tm_simplify_enabled(self._tm))

    @property
    def default_rounding_mode(self):
        return <int>stp_tm_default_rounding_mode(self._tm)

    @default_rounding_mode.setter
    def default_rounding_mode(self, int rm):
        self._check()
        if stp_tm_set_default_rounding_mode(self._tm, <stp_rm>rm) != STP_OK:
            self._fail("stp_tm_set_default_rounding_mode")

    @property
    def uf_sort_width(self):
        return stp_tm_uf_sort_width(self._tm)

    @property
    def owner_thread(self):
        """The ident of the thread that created the manager (informational: a manager may
        be used from any thread, one call at a time)."""
        return self._owner

    @property
    def busy(self):
        """True while a check or a parse runs on this manager (the GIL is released then)."""
        return self._busy

    # ------------------------------------------------------------ sorts
    def bool_sort(self):
        self._check()
        cdef stp_sort h = stp_mk_bool_sort(self._tm)
        if h == NULL:
            self._fail("stp_mk_bool_sort")
        return self._wrap_sort(h)

    def bv_sort(self, width):
        self._check()
        if not isinstance(width, int) or width < 0 or width > 0xFFFFFFFF:
            raise ArgumentError("a bit-vector width must be a positive int, got %r" % (width,))
        cdef stp_sort h = stp_mk_bv_sort(self._tm, <uint32_t>width)
        if h == NULL:
            self._fail("stp_mk_bv_sort")
        return self._wrap_sort(h)

    def fp_sort(self, ebits, sbits):
        self._check()
        if not isinstance(ebits, int) or not isinstance(sbits, int) or ebits < 0 or sbits < 0 \
                or ebits > 0xFFFFFFFF or sbits > 0xFFFFFFFF:
            raise ArgumentError("a floating-point format needs two positive ints, got %r, %r" % (ebits, sbits))
        cdef stp_sort h = stp_mk_fp_sort(self._tm, <uint32_t>ebits, <uint32_t>sbits)
        if h == NULL:
            self._fail("stp_mk_fp_sort")
        return self._wrap_sort(h)

    def rm_sort(self):
        self._check()
        cdef stp_sort h = stp_mk_rm_sort(self._tm)
        if h == NULL:
            self._fail("stp_mk_rm_sort")
        return self._wrap_sort(h)

    def real_sort(self):
        self._check()
        cdef stp_sort h = stp_mk_real_sort(self._tm)
        if h == NULL:
            self._fail("stp_mk_real_sort")
        return self._wrap_sort(h)

    def array_sort(self, Sort index not None, Sort element not None):
        self._check()
        cdef stp_sort h = stp_mk_array_sort(self._tm, index._h, element._h)
        if h == NULL:
            self._fail("stp_mk_array_sort")
        return self._wrap_sort(h)

    def fun_sort(self, list domain not None, Sort codomain not None):
        self._check()
        cdef size_t n = len(domain), i
        cdef stp_sort* dom = <stp_sort*>malloc((n if n > 0 else 1) * sizeof(stp_sort))
        cdef stp_sort h
        if dom == NULL:
            raise MemoryError()
        try:
            for i in range(n):
                if not isinstance(domain[i], Sort):
                    raise TypeError("a function domain is a list of sorts, got %s" % type(domain[i]).__name__)
                dom[i] = (<Sort>domain[i])._h
            h = stp_mk_fun_sort(self._tm, n, dom, codomain._h)
        finally:
            free(dom)
        if h == NULL:
            self._fail("stp_mk_fun_sort")
        return self._wrap_sort(h)

    def declare_sort(self, name):
        self._check()
        cdef bytes b = _b(name)
        cdef stp_sort h = stp_tm_declare_sort(self._tm, b)
        if h == NULL:
            self._fail("stp_tm_declare_sort")
        return self._wrap_sort(h)

    def mk_fresh_sort(self, prefix=""):
        self._check()
        cdef bytes b = _b(prefix)
        cdef stp_sort h = stp_mk_fresh_sort(self._tm, b)
        if h == NULL:
            self._fail("stp_mk_fresh_sort")
        return self._wrap_sort(h)

    def declared_sorts(self):
        self._check()
        cdef size_t n = stp_tm_num_declared_sorts(self._tm), i
        cdef stp_sort h
        out = []
        for i in range(n):
            h = stp_tm_declared_sort_at(self._tm, i)
            if h == NULL:
                self._fail("stp_tm_declared_sort_at")
            out.append(self._wrap_sort(h))
        return out

    # ------------------------------------------------------------ symbols
    def declare(self, name, Sort sort not None):
        self._check()
        cdef bytes b = _b(name)
        cdef stp_term h = stp_declare(self._tm, b, sort._h)
        if h == NULL:
            self._fail("stp_declare")
        return self._wrap(h)

    def mk_fresh(self, Sort sort not None, prefix=""):
        self._check()
        cdef bytes b = _b(prefix)
        cdef stp_term h = stp_mk_fresh(self._tm, sort._h, b)
        if h == NULL:
            self._fail("stp_mk_fresh")
        return self._wrap(h)

    def symbol(self, name):
        self._check()
        cdef bytes b = _b(name)
        cdef stp_term h = stp_tm_symbol(self._tm, b)
        if h == NULL:
            if stp_tm_error(self._tm) != NULL:
                self._fail("stp_tm_symbol")
            return None
        return self._wrap(h)

    def bind_symbol(self, name, Term t not None):
        self._check()
        cdef bytes b = _b(name)
        if stp_tm_bind_symbol(self._tm, b, t._h) != STP_OK:
            self._fail("stp_tm_bind_symbol")

    def symbols(self):
        self._check()
        cdef size_t n = stp_tm_num_symbols(self._tm), i
        cdef stp_term h
        out = []
        for i in range(n):
            h = stp_tm_symbol_at(self._tm, i)
            if h == NULL:
                self._fail("stp_tm_symbol_at")
            out.append(self._wrap(h))
        return out

    def term_from_id(self, id):
        self._check()
        cdef stp_term h = stp_tm_term_from_id(self._tm, <uint64_t>id)
        if h == NULL:
            self._fail("stp_tm_term_from_id")
        return self._wrap(h)

    # ------------------------------------------------------------ values
    def mk_bool(self, v):
        self._check()
        cdef stp_term h = stp_mk_bool(self._tm, 1 if v else 0)
        if h == NULL:
            self._fail("stp_mk_bool")
        return self._wrap(h)

    def mk_bv(self, width, value):
        """A bit-vector value of `width` bits: strict (the two's complement range of the
        width, checked by the C layer); any Python int."""
        self._check()
        if not isinstance(value, int):
            raise TypeError("a bit-vector literal must be an int, got %s" % type(value).__name__)
        cdef stp_term h
        cdef uint32_t w = <uint32_t>width
        cdef bytes digits
        if 0 <= value <= UINT64_MAX:
            h = stp_mk_bv_uint64(self._tm, w, <uint64_t>value)
        elif INT64_MIN <= value < 0:
            h = stp_mk_bv_int64(self._tm, w, <int64_t>value)
        else:
            digits = str(value).encode("ascii")
            h = stp_mk_bv_str(self._tm, w, digits, 10)
        if h == NULL:
            self._fail("stp_mk_bv")
        return self._wrap(h)

    def mk_bv_str(self, width, digits, base=10):
        self._check()
        cdef bytes b = _b(digits)
        cdef stp_term h = stp_mk_bv_str(self._tm, <uint32_t>width, b, <int>base)
        if h == NULL:
            self._fail("stp_mk_bv_str")
        return self._wrap(h)

    def mk_bv_bytes(self, width, data, little_endian=True):
        self._check()
        cdef bytes b = bytes(data)
        cdef stp_term h = stp_mk_bv_bytes(self._tm, <uint32_t>width, len(b), <const uint8_t*><char*>b,
                                          1 if little_endian else 0)
        if h == NULL:
            self._fail("stp_mk_bv_bytes")
        return self._wrap(h)

    def mk_fp_double(self, Sort fp not None, int rm, double value):
        self._check()
        cdef stp_term h = stp_mk_fp_double(self._tm, fp._h, <stp_rm>rm, value)
        if h == NULL:
            self._fail("stp_mk_fp_double")
        return self._wrap(h)

    def mk_fp_decimal(self, Sort fp not None, int rm, literal):
        self._check()
        cdef bytes b = _b(literal)
        cdef stp_term h = stp_mk_fp_decimal(self._tm, fp._h, <stp_rm>rm, b)
        if h == NULL:
            self._fail("stp_mk_fp_decimal")
        return self._wrap(h)

    def mk_fp_from_bits(self, Sort fp not None, Term bv not None):
        self._check()
        cdef stp_term h = stp_mk_fp_from_bits(self._tm, fp._h, bv._h)
        if h == NULL:
            self._fail("stp_mk_fp_from_bits")
        return self._wrap(h)

    def mk_fp_from_bits_str(self, Sort fp not None, bits):
        self._check()
        cdef bytes b = _b(bits)
        cdef stp_term h = stp_mk_fp_from_bits_str(self._tm, fp._h, b)
        if h == NULL:
            self._fail("stp_mk_fp_from_bits_str")
        return self._wrap(h)

    def mk_fp_special(self, Sort fp not None, which):
        """which: 'nan', '+zero', '-zero', '+inf', '-inf'."""
        self._check()
        cdef stp_term h
        if which == "nan":
            h = stp_mk_fp_nan(self._tm, fp._h)
        elif which == "+zero":
            h = stp_mk_fp_pos_zero(self._tm, fp._h)
        elif which == "-zero":
            h = stp_mk_fp_neg_zero(self._tm, fp._h)
        elif which == "+inf":
            h = stp_mk_fp_pos_inf(self._tm, fp._h)
        elif which == "-inf":
            h = stp_mk_fp_neg_inf(self._tm, fp._h)
        else:
            raise ArgumentError("unknown special float %r" % (which,))
        if h == NULL:
            self._fail("stp_mk_fp_special")
        return self._wrap(h)

    def mk_rm(self, int rm):
        self._check()
        cdef stp_term h = stp_mk_rm(self._tm, <stp_rm>rm)
        if h == NULL:
            self._fail("stp_mk_rm")
        return self._wrap(h)

    def mk_real_str(self, literal):
        self._check()
        cdef bytes b = _b(literal)
        cdef stp_term h = stp_mk_real_str(self._tm, b)
        if h == NULL:
            self._fail("stp_mk_real_str")
        return self._wrap(h)

    def mk_const_array(self, Sort array_sort not None, Term element not None):
        self._check()
        cdef stp_term h = stp_mk_const_array(self._tm, array_sort._h, element._h)
        if h == NULL:
            self._fail("stp_mk_const_array")
        return self._wrap(h)

    def array_from_bytes(self, data, index_width=32):
        self._check()
        cdef bytes b = bytes(data)
        cdef stp_term h = stp_array_from_bytes(self._tm, len(b), <const uint8_t*><char*>b, <uint32_t>index_width)
        if h == NULL:
            self._fail("stp_array_from_bytes")
        return self._wrap(h)

    # ------------------------------------------------------------ construction
    def mk_term(self, int kind, list args not None, indices=(), Sort sort=None):
        """The generic constructor: stp_mk_term_sorted(kind, args, indices, sort)."""
        self._check()
        return self._mk(<stp_kind>kind, args, tuple(indices), sort, "stp_mk_term")

    def rewrap(self, Term t not None, cls):
        """A NEW wrapper of t's node of class `cls` (a Term subclass), holding its own
        reference and not entered in the identity map: for value views that decorate a
        term (an array value is the store chain it denotes plus its entries)."""
        self._check()
        if not (isinstance(cls, type) and issubclass(cls, Term)):
            raise TypeError("rewrap needs a Term subclass")
        cdef stp_term h = stp_term_copy(t._h)
        if h == NULL:
            self._fail("stp_term_copy")
        obj = cls.__new__(cls)
        (<Term>obj)._h = h
        (<Term>obj)._m = self
        (<Term>obj)._key = <size_t>self._tm
        return obj

    def simplify_term(self, Term t not None):
        self._check()
        cdef stp_term h = stp_tm_simplify(self._tm, t._h)
        if h == NULL:
            self._fail("stp_tm_simplify")
        return self._wrap(h)

    def substitute(self, Term t not None, list from_ not None, list to not None):
        self._check()
        if len(from_) != len(to):
            raise ArgumentError("substitute: %d sources for %d targets" % (len(from_), len(to)))
        cdef size_t n = 0, m = 0
        cdef stp_term* a = self._array(from_, &n, "stp_term_substitute")
        cdef stp_term* b
        cdef stp_term h
        try:
            b = self._array(to, &m, "stp_term_substitute")
        except BaseException:
            free(a)
            raise
        try:
            h = stp_term_substitute(t._h, n, a, b)
        finally:
            free(a)
            free(b)
        if h == NULL:
            self._fail("stp_term_substitute")
        return self._wrap(h)

    # ------------------------------------------------------------ the error record (diagnostics)
    def pending_error(self):
        """The manager's recorded error as an exception object, or None (never raised, never cleared)."""
        cdef const stp_error* e = stp_tm_error(self._tm)
        if e == NULL:
            return None
        return _exc_from(e, self, True)

    def clear_error(self):
        stp_tm_clear_error(self._tm)


# ----------------------------------------------------------------- Sort

cdef class Sort:
    """A sort handle (pooled by its manager: the same sort is always the same object)."""

    def __cinit__(self, *args, **kwargs):
        self._h = NULL
        self._m = None

    def _manager(self):
        return self._m

    @property
    def id(self):
        return stp_sort_id(self._h)

    def kind(self):
        cdef stp_sort_kind k
        if stp_sort_get_kind(self._h, &k) != STP_OK:
            self._m._fail("stp_sort_get_kind")
        return <int>k

    def bv_size(self):
        cdef uint32_t n
        if stp_sort_bv_size(self._h, &n) != STP_OK:
            self._m._fail("stp_sort_bv_size")
        return n

    def fp_ebits(self):
        cdef uint32_t n
        if stp_sort_fp_exp_size(self._h, &n) != STP_OK:
            self._m._fail("stp_sort_fp_exp_size")
        return n

    def fp_sbits(self):
        cdef uint32_t n
        if stp_sort_fp_sig_size(self._h, &n) != STP_OK:
            self._m._fail("stp_sort_fp_sig_size")
        return n

    def array_index(self):
        cdef stp_sort h = stp_sort_array_index(self._h)
        if h == NULL:
            self._m._fail("stp_sort_array_index")
        return self._m._wrap_sort(h)

    def array_element(self):
        cdef stp_sort h = stp_sort_array_element(self._h)
        if h == NULL:
            self._m._fail("stp_sort_array_element")
        return self._m._wrap_sort(h)

    def fun_arity(self):
        cdef uint32_t n
        if stp_sort_fun_arity(self._h, &n) != STP_OK:
            self._m._fail("stp_sort_fun_arity")
        return n

    def fun_domain(self, i):
        cdef stp_sort h = stp_sort_fun_domain(self._h, <uint32_t>i)
        if h == NULL:
            self._m._fail("stp_sort_fun_domain")
        return self._m._wrap_sort(h)

    def fun_codomain(self):
        cdef stp_sort h = stp_sort_fun_codomain(self._h)
        if h == NULL:
            self._m._fail("stp_sort_fun_codomain")
        return self._m._wrap_sort(h)

    def uninterpreted_name(self):
        cdef char* p = stp_sort_name(self._h)
        if p == NULL:
            self._m._fail("stp_sort_name")
        return _take(p)

    def sexpr(self):
        cdef char* p = stp_sort_str(self._h)
        if p == NULL:
            self._m._fail("stp_sort_str")
        return _take(p)

    def same(self, Sort other):
        return other is not None and other._h == self._h


# ----------------------------------------------------------------- Term

cdef class Term:
    """A term handle: one wrapper per live node of a manager (identity is term identity)."""

    def __cinit__(self, *args, **kwargs):
        self._h = NULL
        self._m = None

    def __dealloc__(self):
        # Released at once while no check runs on the manager (the GIL serialises this
        # finaliser with every other use of it); otherwise (a check in progress, or the
        # manager reference already cleared by the cyclic garbage collector) queued for
        # the manager's next entry point.
        cdef Manager m
        if self._h != NULL:
            m = self._m
            if m is not None and not m._busy:
                stp_term_release(self._h)
            else:
                _defer(self._key, DEFER_TERM, <void*>self._h)
            self._h = NULL

    def _manager(self):
        return self._m

    @property
    def id(self):
        return stp_term_id(self._h)

    def node_hash(self):
        return stp_term_hash(self._h)

    def kind(self):
        cdef stp_kind k
        if stp_term_get_kind(self._h, &k) != STP_OK:
            self._m._fail("stp_term_get_kind")
        return <int>k

    def sort(self):
        cdef stp_sort h = stp_term_sort(self._h)
        if h == NULL:
            self._m._fail("stp_term_sort")
        return self._m._wrap_sort(h)

    def sort_kind(self):
        """The sort kind in one call (the class chooser's view)."""
        cdef stp_sort h = stp_term_sort(self._h)
        cdef stp_sort_kind k
        if h == NULL or stp_sort_get_kind(h, &k) != STP_OK:
            self._m._fail("stp_term_sort")
        return <int>k

    def num_children(self):
        cdef size_t n
        if stp_term_num_children(self._h, &n) != STP_OK:
            self._m._fail("stp_term_num_children")
        return n

    def child(self, i):
        cdef size_t n
        if stp_term_num_children(self._h, &n) != STP_OK:
            self._m._fail("stp_term_num_children")
        if not isinstance(i, int):
            raise TypeError("child index must be an int")
        if i < 0:
            i += n
        if i < 0 or <size_t>i >= n:
            raise IndexError("child index %d out of range for a term with %d children" % (i, n))
        cdef stp_term h = stp_term_child(self._h, <size_t>i)
        if h == NULL:
            self._m._fail("stp_term_child")
        return self._m._wrap(h)

    def children(self):
        cdef size_t n, i
        cdef stp_term h
        if stp_term_num_children(self._h, &n) != STP_OK:
            self._m._fail("stp_term_num_children")
        out = []
        for i in range(n):
            h = stp_term_child(self._h, i)
            if h == NULL:
                self._m._fail("stp_term_child")
            out.append(self._m._wrap(h))
        return out

    def indices(self):
        cdef size_t n, i
        cdef uint32_t v
        if stp_term_num_indices(self._h, &n) != STP_OK:
            self._m._fail("stp_term_num_indices")
        out = []
        for i in range(n):
            if stp_term_index(self._h, i, &v) != STP_OK:
                self._m._fail("stp_term_index")
            out.append(v)
        return out

    def is_value(self):
        return bool(stp_term_is_value(self._h))

    def is_const(self):
        return bool(stp_term_is_const(self._h))

    def symbol(self):
        cdef char* p = stp_term_symbol(self._h)
        if p == NULL:
            if stp_tm_error(self._m._tm) != NULL:
                self._m._fail("stp_term_symbol")
            return None
        return _take(p)

    def sexpr(self):
        """SMT-LIB 2, untruncated."""
        cdef char* p = stp_term_str(self._h)
        if p == NULL:
            self._m._fail("stp_term_str")
        return _take(p)

    def to_string(self, int format, share_subterms=False):
        cdef char* p = stp_term_to_string(self._h, <stp_format>format, 1 if share_subterms else 0)
        if p == NULL:
            self._m._fail("stp_term_to_string")
        return _take(p)

    def same(self, other):
        if not isinstance(other, Term):
            return False
        return bool(stp_term_same(self._h, (<Term>other)._h))

    # ------------------------------------------------------------ readers
    def to_bool(self):
        cdef cbool v
        if stp_term_to_bool(self._h, &v) != STP_OK:
            self._m._fail("stp_term_to_bool")
        return bool(v)

    def fits_uint64(self):
        return bool(stp_term_fits_uint64(self._h))

    def fits_int64(self):
        return bool(stp_term_fits_int64(self._h))

    def to_uint64(self):
        cdef uint64_t v
        if stp_term_to_uint64(self._h, &v) != STP_OK:
            self._m._fail("stp_term_to_uint64")
        return v

    def to_int64(self):
        cdef int64_t v
        if stp_term_to_int64(self._h, &v) != STP_OK:
            self._m._fail("stp_term_to_int64")
        return v

    def to_bv_string(self, int base=2, pad=True):
        cdef char* p = stp_term_to_bv_string(self._h, base, 1 if pad else 0)
        if p == NULL:
            self._m._fail("stp_term_to_bv_string")
        return _take(p)

    def to_uint(self):
        """The unsigned value of a BV value as a Python int, any width."""
        cdef uint64_t v
        if stp_term_fits_uint64(self._h):
            if stp_term_to_uint64(self._h, &v) != STP_OK:
                self._m._fail("stp_term_to_uint64")
            return v
        return int(self.to_bv_string(16, True), 16)

    def to_int(self):
        """The two's complement value of a BV value as a Python int, any width."""
        cdef int64_t v
        cdef uint32_t w
        cdef stp_sort s
        if stp_term_fits_int64(self._h):
            if stp_term_to_int64(self._h, &v) != STP_OK:
                self._m._fail("stp_term_to_int64")
            return v
        s = stp_term_sort(self._h)
        if s == NULL or stp_sort_bv_size(s, &w) != STP_OK:
            self._m._fail("stp_sort_bv_size")
        return _int_from_hex(self.to_bv_string(16, True), True, w)

    def to_bv_bytes(self, little_endian=True):
        cdef uint32_t w
        cdef stp_sort s = stp_term_sort(self._h)
        if s == NULL or stp_sort_bv_size(s, &w) != STP_OK:
            self._m._fail("stp_sort_bv_size")
        cdef size_t n = (w + 7) // 8
        cdef bytes out = PyBytes_FromStringAndSize(NULL, n)
        if stp_term_to_bv_bytes(self._h, n, <uint8_t*><char*>out, 1 if little_endian else 0) != STP_OK:
            self._m._fail("stp_term_to_bv_bytes")
        return out

    def to_fp(self):
        """(exp_size, sig_size, sign, biased_exponent, class, significand) of an FP value."""
        cdef stp_float_value v
        cdef size_t n, i
        cdef uint64_t* limbs
        if stp_term_to_fp(self._h, &v) != STP_OK:
            self._m._fail("stp_term_to_fp")
        n = (v.sig_size - 1 + 63) // 64
        sig = 0
        if n > 0:
            limbs = <uint64_t*>malloc(n * sizeof(uint64_t))
            if limbs == NULL:
                raise MemoryError()
            try:
                if stp_term_fp_significand_limbs(self._h, n, limbs) != STP_OK:
                    self._m._fail("stp_term_fp_significand_limbs")
                for i in range(n):
                    sig |= (<object>limbs[i]) << (64 * i)
            finally:
                free(limbs)
        return (v.exp_size, v.sig_size, bool(v.sign), v.biased_exponent, <int>v.cls, sig)

    def fp_bits(self):
        cdef char* p = stp_term_fp_bits(self._h)
        if p == NULL:
            self._m._fail("stp_term_fp_bits")
        return _take(p)

    def fp_to_double(self):
        cdef double d
        if stp_term_fp_to_double(self._h, &d) != STP_OK:
            self._m._fail("stp_term_fp_to_double")
        return d

    def fp_to_rational(self):
        cdef char* num = NULL
        cdef char* den = NULL
        if stp_term_fp_to_rational(self._h, &num, &den) != STP_OK:
            self._m._fail("stp_term_fp_to_rational")
        return (_take(num), _take(den))

    def to_rm(self):
        cdef stp_rm v
        if stp_term_to_rm(self._h, &v) != STP_OK:
            self._m._fail("stp_term_to_rm")
        return <int>v

    def real_numerator(self):
        cdef char* p = stp_term_real_numerator(self._h)
        if p == NULL:
            self._m._fail("stp_term_real_numerator")
        return _take(p)

    def real_denominator(self):
        cdef char* p = stp_term_real_denominator(self._h)
        if p == NULL:
            self._m._fail("stp_term_real_denominator")
        return _take(p)

    def real_to_double(self):
        cdef double d
        if stp_term_real_to_double(self._h, &d) != STP_OK:
            self._m._fail("stp_term_real_to_double")
        return d

    def to_uninterpreted_index(self):
        cdef uint64_t v
        if stp_term_to_uninterpreted_index(self._h, &v) != STP_OK:
            self._m._fail("stp_term_to_uninterpreted_index")
        return v


# ----------------------------------------------------------------- Options

cdef class OptionsHandle:
    """A standalone stp_options value (its own error record)."""

    def __cinit__(self, *args, **kwargs):
        self._o = NULL

    def __init__(self, OptionsHandle copy_of=None):
        if self._o != NULL:
            return
        if copy_of is not None:
            self._o = stp_options_copy(copy_of._o)
        else:
            self._o = stp_options_new()
        if self._o == NULL:
            _raise_thread_local("stp_options_new")

    def __dealloc__(self):
        if self._o != NULL:
            stp_options_delete(self._o)
            self._o = NULL

    cdef int _fail(self, const char* fn) except -1:
        cdef const stp_error* e = stp_options_error(self._o)
        if e == NULL:
            raise InternalError("'%s' failed without recording an error" % _s(fn))
        exc = _exc_from(e, None, False)
        stp_options_clear_error(self._o)
        raise exc

    def copy(self):
        return OptionsHandle(self)

    def set_str(self, name, value):
        cdef bytes n = _b(name), v = _b(value)
        if stp_options_set_str(self._o, n, v) != STP_OK:
            self._fail("stp_options_set_str")

    def set_bool(self, name, value):
        cdef bytes n = _b(name)
        if stp_options_set_bool(self._o, n, 1 if value else 0) != STP_OK:
            self._fail("stp_options_set_bool")

    def set_int64(self, name, value):
        cdef bytes n = _b(name)
        if stp_options_set_int64(self._o, n, <int64_t>value) != STP_OK:
            self._fail("stp_options_set_int64")

    def set_uint64(self, name, value):
        cdef bytes n = _b(name)
        if stp_options_set_uint64(self._o, n, <uint64_t>value) != STP_OK:
            self._fail("stp_options_set_uint64")

    def set_duration_ms(self, name, value):
        cdef bytes n = _b(name)
        if stp_options_set_duration_ms(self._o, n, <uint64_t>value) != STP_OK:
            self._fail("stp_options_set_duration_ms")

    def set_names(self, name, members):
        cdef bytes n = _b(name)
        cdef list bs = [_b(m) for m in members]
        cdef size_t k = len(bs), i
        cdef const char** arr = <const char**>malloc((k if k > 0 else 1) * sizeof(char*))
        if arr == NULL:
            raise MemoryError()
        try:
            for i in range(k):
                arr[i] = <const char*>(<bytes>bs[i])
            if stp_options_set_names(self._o, n, k, arr) != STP_OK:
                self._fail("stp_options_set_names")
        finally:
            free(arr)

    def set_args(self, argv):
        cdef list bs = [_b(a) for a in argv]
        cdef int k = len(bs), i
        cdef const char** arr = <const char**>malloc((k if k > 0 else 1) * sizeof(char*))
        if arr == NULL:
            raise MemoryError()
        try:
            for i in range(k):
                arr[i] = <const char*>(<bytes>bs[i])
            if stp_options_set_args(self._o, k, arr) != STP_OK:
                self._fail("stp_options_set_args")
        finally:
            free(arr)

    def get_str(self, name):
        cdef bytes n = _b(name)
        cdef char* p = stp_options_get_str(self._o, n)
        if p == NULL:
            self._fail("stp_options_get_str")
        return _take(p)

    def get_bool(self, name):
        cdef bytes n = _b(name)
        cdef cbool v
        if stp_options_get_bool(self._o, n, &v) != STP_OK:
            self._fail("stp_options_get_bool")
        return bool(v)

    def get_int64(self, name):
        cdef bytes n = _b(name)
        cdef int64_t v
        if stp_options_get_int64(self._o, n, &v) != STP_OK:
            self._fail("stp_options_get_int64")
        return v

    def get_uint64(self, name):
        cdef bytes n = _b(name)
        cdef uint64_t v
        if stp_options_get_uint64(self._o, n, &v) != STP_OK:
            self._fail("stp_options_get_uint64")
        return v

    def get_duration_ms(self, name):
        cdef bytes n = _b(name)
        cdef uint64_t v
        if stp_options_get_duration_ms(self._o, n, &v) != STP_OK:
            self._fail("stp_options_get_duration_ms")
        return v

    def resolved_str(self, name):
        cdef bytes n = _b(name)
        cdef char* p = stp_options_resolved_str(self._o, n)
        if p == NULL:
            self._fail("stp_options_resolved_str")
        return _take(p)

    def is_set(self, name):
        cdef bytes n = _b(name)
        cdef bint v = stp_options_is_set(self._o, n)
        if stp_options_error(self._o) != NULL:
            self._fail("stp_options_is_set")
        return bool(v)

    def reset(self, name):
        cdef bytes n = _b(name)
        if stp_options_reset(self._o, n) != STP_OK:
            self._fail("stp_options_reset")

    def reset_all(self):
        stp_options_reset_all(self._o)

    def resolve(self):
        if stp_options_resolve(self._o) != STP_OK:
            self._fail("stp_options_resolve")


def option_names(int tier=-1):
    """The registry names of a tier (-1: every tier), in table order."""
    cdef size_t n = stp_options_num_names(tier), i
    cdef const char* p
    out = []
    for i in range(n):
        p = stp_options_name(tier, i)
        if p != NULL:
            out.append(_s(p))
    return out


def option_help(int tier=-1):
    cdef char* p = stp_options_help(tier)
    if p == NULL:
        _raise_thread_local("stp_options_help")
    return _take(p)


def option_exists(name):
    cdef bytes n = _b(name)
    return stp_option_info_type(n) != NULL


def option_info(name):
    """Every registry field of one option as a dict; UnknownOption for an unknown name."""
    cdef bytes n = _b(name)
    cdef const char* t = stp_option_info_type(n)
    cdef cbool has_min = 0, has_max = 0
    cdef int64_t lo = 0, hi = 0
    cdef size_t k, i
    if t == NULL:
        _raise_thread_local("stp_option_info_type")
    info = {
        "name": name,
        "type": _s(t),
        "python_key": _s(stp_option_info_python_key(n)),
        "default": _take(stp_option_info_default(n)),
        "tier": <int>stp_option_info_tier(n),
        "settable": <int>stp_option_info_settable(n),
        "scope": <int>stp_option_info_scope(n),
        "category": _s(stp_option_info_category(n)) or "",
        "help": _s(stp_option_info_help(n)) or "",
        "supported": bool(stp_option_info_supported(n)),
        "short": _s(stp_option_info_short(n)) or "",
        "negation": _s(stp_option_info_negation(n)) or "",
    }
    info["min"] = None
    info["max"] = None
    if info["type"] in ("int", "uint") and stp_option_info_range(n, &has_min, &lo, &has_max, &hi) == STP_OK:
        info["min"] = lo if has_min else None
        info["max"] = hi if has_max else None
    k = stp_option_info_num_values(n)
    info["values"] = [_s(stp_option_info_value(n, i)) for i in range(k)]
    k = stp_option_info_num_aliases(n)
    info["aliases"] = [_s(stp_option_info_alias(n, i)) for i in range(k)]
    return info


# ----------------------------------------------------------------- callbacks

cdef cbool _terminator_cb(void* user) noexcept with gil:
    cdef CallbackBox* box = <CallbackBox*>user
    cdef SolverHandle s
    if box.owner == NULL:
        return 0
    s = <SolverHandle>box.owner
    try:
        if s._terminator is None:
            return 0
        return 1 if s._terminator() else 0
    except BaseException as e:
        s._callback_error = e
        return 1


cdef void _sink_cb(const char* text, size_t n, void* user) noexcept with gil:
    cdef CallbackBox* box = <CallbackBox*>user
    cdef SolverHandle s
    if box.owner == NULL:
        return
    s = <SolverHandle>box.owner
    try:
        if s._sink is not None:
            s._sink(PyBytes_FromStringAndSize(text, n).decode("utf-8", "replace"))
    except BaseException:
        traceback.print_exc()


cdef void _out_sink_cb(const char* text, size_t n, void* user) noexcept with gil:
    cdef CallbackBox* box = <CallbackBox*>user
    cdef SolverHandle s
    if box.owner == NULL:
        return
    s = <SolverHandle>box.owner
    try:
        if s._out_sink is not None:
            s._out_sink(PyBytes_FromStringAndSize(text, n).decode("utf-8", "replace"))
    except BaseException:
        traceback.print_exc()


cdef void _fatal_cb(const char* message, void* user) noexcept with gil:
    cdef CallbackBox* box = <CallbackBox*>user
    cdef SolverHandle s
    if box.owner == NULL:
        return
    s = <SolverHandle>box.owner
    try:
        if s._fatal_handler is not None:
            s._fatal_handler(PyBytes_FromStringAndSize(message, strlen(message))
                             .decode("utf-8", "replace"))
    except BaseException:
        traceback.print_exc()


_CNF_SCOPES = {STP_CNF_WHOLE: "whole", STP_CNF_PARTIAL: "partial",
               STP_CNF_OVER_APPROXIMATION: "over-approximation"}


cdef void _cnf_cb(const char* dimacs, size_t n, stp_cnf_scope scope, void* user) noexcept with gil:
    cdef CallbackBox* box = <CallbackBox*>user
    cdef SolverHandle s
    if box.owner == NULL:
        return
    s = <SolverHandle>box.owner
    try:
        if s._cnf_sink is not None:
            s._cnf_sink(PyBytes_FromStringAndSize(dimacs, n), _CNF_SCOPES.get(<int>scope, "whole"))
    except BaseException:
        traceback.print_exc()


# A parse's input: text already in memory, read without the GIL ...
ctypedef struct _TextSource:
    const char* data
    size_t size
    size_t offset


cdef size_t _text_source_cb(char* buf, size_t max, void* user) noexcept nogil:
    cdef _TextSource* src = <_TextSource*>user
    cdef size_t k = src.size - src.offset
    if k > max:
        k = max
    memcpy(buf, src.data + src.offset, k)
    src.offset += k
    return k


# ... or a stream, read as its data arrives: read1 where the stream has it (a binary stream
# hands out what it holds), a line at a time otherwise (a text stream such as sys.stdin), so a
# script arriving over a pipe is run command by command.
cdef class _StreamSource:
    cdef object _read
    cdef bint _lines
    cdef bytes _pending
    cdef object error

    def __cinit__(self, stream):
        if hasattr(stream, "read1"):
            self._read, self._lines = stream.read1, False
        elif hasattr(stream, "readline"):
            self._read, self._lines = stream.readline, True
        elif hasattr(stream, "read"):
            self._read, self._lines = stream.read, False
        else:
            raise TypeError("expected a str, bytes or a readable stream, got %s"
                            % type(stream).__name__)
        self._pending = b""
        self.error = None


cdef size_t _stream_source_cb(char* buf, size_t max, void* user) noexcept with gil:
    cdef _StreamSource src = <_StreamSource>user
    cdef object chunk
    cdef size_t k
    try:
        if not src._pending:
            chunk = src._read() if src._lines else src._read(max)
            if isinstance(chunk, str):
                chunk = (<str>chunk).encode("utf-8")
            if not chunk:
                return 0
            src._pending = bytes(chunk)
        k = min(<size_t>len(src._pending), max)
        memcpy(buf, <const char*>src._pending, k)
        src._pending = src._pending[k:]
        return k
    except BaseException as e:
        src.error = e
        return <size_t>-1


cdef void _collect_cb(const char* text, size_t n, void* user) noexcept with gil:
    try:
        (<list>user).append(PyBytes_FromStringAndSize(text, n))
    except BaseException:
        pass


# ----------------------------------------------------------------- Solver

cdef class SolverHandle:
    """A solver (stp_solver) over a Manager; any number may be live over one manager, each
    with its own assertion stack, options and models."""

    def __cinit__(self, *args, **kwargs):
        self._s = NULL
        self._box = <CallbackBox*>malloc(sizeof(CallbackBox))
        if self._box == NULL:
            raise MemoryError()
        self._box.owner = <void*>self
        self._m = None
        self._terminator = None
        self._sink = None
        self._out_sink = None
        self._fatal_handler = None
        self._cnf_sink = None
        self._callback_error = None

    def __init__(self, Manager tm not None, OptionsHandle options=None):
        if self._s != NULL:
            return
        tm._check()
        self._s = stp_solver_new(tm._tm, options._o if options is not None else NULL)
        if self._s == NULL:
            tm._fail("stp_solver_new")
        self._m = tm
        self._key = <size_t>tm._tm

    def __dealloc__(self):
        cdef Manager m
        if self._box != NULL:
            self._box.owner = NULL  # a callback from here on finds no solver
        if self._s != NULL:
            m = self._m
            if m is not None and not m._busy:
                stp_solver_delete(self._s)
                free(self._box)
            else:
                # the box outlives the deferred delete, which may still call back
                _defer(self._key, DEFER_SOLVER, <void*>self._s)
                _defer(self._key, DEFER_BOX, <void*>self._box)
            self._s = NULL
        else:
            free(self._box)
        self._box = NULL

    cdef int _live(self) except -1:
        if self._s == NULL:
            raise StateError("the solver is closed")
        self._m._check()
        return 0

    cdef int _fail_mutate(self, const char* fn) except -1:
        # A raised exception cannot be ignored, so the failed state has done its job.
        cdef const stp_error* e = stp_tm_error(self._m._tm)
        cdef object exc
        stp_solver_clear_error(self._s)
        if e == NULL:
            raise InternalError("'%s' failed without recording an error" % _s(fn))
        exc = _exc_from(e, self._m, True)
        stp_tm_clear_error(self._m._tm)
        raise exc

    def _manager(self):
        return self._m

    def close(self):
        """Delete the solver now (idempotent); terms, sorts and models stay valid."""
        if self._s != NULL:
            self._m._check()
            stp_solver_delete(self._s)
            self._s = NULL
            self._terminator = None
            self._sink = None
            self._out_sink = None
            self._fatal_handler = None
            self._cnf_sink = None

    @property
    def closed(self):
        return self._s == NULL

    # ------------------------------------------------------------ live options
    def set_str(self, name, value):
        self._live()
        cdef bytes n = _b(name), v = _b(value)
        if stp_solver_set_str(self._s, n, v) != STP_OK:
            self._fail_mutate("stp_solver_set_str")

    def set_bool(self, name, value):
        self._live()
        cdef bytes n = _b(name)
        if stp_solver_set_bool(self._s, n, 1 if value else 0) != STP_OK:
            self._fail_mutate("stp_solver_set_bool")

    def set_int64(self, name, value):
        self._live()
        cdef bytes n = _b(name)
        if stp_solver_set_int64(self._s, n, <int64_t>value) != STP_OK:
            self._fail_mutate("stp_solver_set_int64")

    def set_uint64(self, name, value):
        self._live()
        cdef bytes n = _b(name)
        if stp_solver_set_uint64(self._s, n, <uint64_t>value) != STP_OK:
            self._fail_mutate("stp_solver_set_uint64")

    def set_duration_ms(self, name, value):
        self._live()
        cdef bytes n = _b(name)
        if stp_solver_set_duration_ms(self._s, n, <uint64_t>value) != STP_OK:
            self._fail_mutate("stp_solver_set_duration_ms")

    def set_names(self, name, members):
        self._live()
        cdef bytes n = _b(name)
        cdef list bs = [_b(m) for m in members]
        cdef size_t k = len(bs), i
        cdef const char** arr = <const char**>malloc((k if k > 0 else 1) * sizeof(char*))
        if arr == NULL:
            raise MemoryError()
        try:
            for i in range(k):
                arr[i] = <const char*>(<bytes>bs[i])
            if stp_solver_set_names(self._s, n, k, arr) != STP_OK:
                self._fail_mutate("stp_solver_set_names")
        finally:
            free(arr)

    def set_args(self, argv):
        self._live()
        cdef list bs = [_b(a) for a in argv]
        cdef int k = len(bs), i
        cdef const char** arr = <const char**>malloc((k if k > 0 else 1) * sizeof(char*))
        if arr == NULL:
            raise MemoryError()
        try:
            for i in range(k):
                arr[i] = <const char*>(<bytes>bs[i])
            if stp_solver_set_args(self._s, k, arr) != STP_OK:
                self._fail_mutate("stp_solver_set_args")
        finally:
            free(arr)

    def get_str(self, name):
        self._live()
        cdef bytes n = _b(name)
        cdef char* p = stp_solver_get_str(self._s, n)
        if p == NULL:
            self._m._fail("stp_solver_get_str")
        return _take(p)

    def get_bool(self, name):
        self._live()
        cdef bytes n = _b(name)
        cdef cbool v
        if stp_solver_get_bool(self._s, n, &v) != STP_OK:
            self._m._fail("stp_solver_get_bool")
        return bool(v)

    def get_int64(self, name):
        self._live()
        cdef bytes n = _b(name)
        cdef int64_t v
        if stp_solver_get_int64(self._s, n, &v) != STP_OK:
            self._m._fail("stp_solver_get_int64")
        return v

    def get_uint64(self, name):
        self._live()
        cdef bytes n = _b(name)
        cdef uint64_t v
        if stp_solver_get_uint64(self._s, n, &v) != STP_OK:
            self._m._fail("stp_solver_get_uint64")
        return v

    def get_duration_ms(self, name):
        self._live()
        cdef bytes n = _b(name)
        cdef uint64_t v
        if stp_solver_get_duration_ms(self._s, n, &v) != STP_OK:
            self._m._fail("stp_solver_get_duration_ms")
        return v

    def resolved_str(self, name):
        self._live()
        cdef bytes n = _b(name)
        cdef char* p = stp_solver_resolved_str(self._s, n)
        if p == NULL:
            self._m._fail("stp_solver_resolved_str")
        return _take(p)

    def is_set(self, name):
        self._live()
        cdef bytes n = _b(name)
        cdef bint v = stp_solver_option_is_set(self._s, n)
        if stp_tm_error(self._m._tm) != NULL:
            self._m._fail("stp_solver_option_is_set")
        return bool(v)

    def reset_option(self, name):
        self._live()
        cdef bytes n = _b(name)
        if stp_solver_reset_option(self._s, n) != STP_OK:
            self._fail_mutate("stp_solver_reset_option")

    def options_copy(self):
        self._live()
        cdef stp_options o = stp_solver_options_copy(self._s)
        if o == NULL:
            self._m._fail("stp_solver_options_copy")
        cdef OptionsHandle h = OptionsHandle.__new__(OptionsHandle)
        h._o = o
        return h

    # ------------------------------------------------------------ assertions
    def assert_(self, Term t not None):
        self._live()
        if stp_solver_assert(self._s, t._h) != STP_OK:
            self._fail_mutate("stp_solver_assert")

    def push(self, n=1):
        self._live()
        if stp_solver_push(self._s, <uint32_t>n) != STP_OK:
            self._fail_mutate("stp_solver_push")

    def pop(self, n=1):
        self._live()
        if stp_solver_pop(self._s, <uint32_t>n) != STP_OK:
            self._fail_mutate("stp_solver_pop")

    def level(self):
        self._live()
        return stp_solver_level(self._s)

    def assertions(self):
        self._live()
        cdef size_t n = stp_solver_num_assertions(self._s), i
        cdef stp_term h
        out = []
        for i in range(n):
            h = stp_solver_assertion(self._s, i)
            if h == NULL:
                self._m._fail("stp_solver_assertion")
            out.append(self._m._wrap(h))
        return out

    def reset_assertions(self):
        self._live()
        if stp_solver_reset_assertions(self._s) != STP_OK:
            self._fail_mutate("stp_solver_reset_assertions")

    def reset(self):
        self._live()
        if stp_solver_reset(self._s) != STP_OK:
            self._fail_mutate("stp_solver_reset")

    # ------------------------------------------------------------ checks
    def check_sat(self, list assumptions=None, timeout=None, conflicts=None):
        """(verdict, reason, message): verdict 1 sat / 2 unsat / 3 unknown. Releases the GIL.
        On the main thread Ctrl-C interrupts the check and raises KeyboardInterrupt."""
        self._live()
        cdef stp_budget budget
        cdef const stp_budget* bp = NULL
        cdef stp_result r
        cdef stp_status st
        cdef size_t n = 0
        cdef stp_term* arr = self._m._array(assumptions if assumptions is not None else [], &n,
                                            "stp_solver_check_sat")
        cdef bint main_thread = 0
        cdef sighandler_t old = SIG_ERR
        if timeout is not None or conflicts is not None:
            budget.has_time = timeout is not None
            budget.time_ms = <uint64_t>(timeout if timeout is not None else 0)
            budget.has_conflicts = conflicts is not None
            budget.conflicts = <uint64_t>(conflicts if conflicts is not None else 0)
            bp = &budget
        self._callback_error = None
        global stp_py_sigint_fired, stp_py_sigint_target
        try:
            main_thread = threading.current_thread() is threading.main_thread()
            if main_thread:
                stp_py_sigint_fired = 0
                stp_py_sigint_target = self._s
                old = signal(SIGINT, stp_py_sigint_handler)
            _set_busy(self._m, True)
            try:
                with nogil:
                    st = stp_solver_check_sat_budget(self._s, n, arr, bp, &r)
            finally:
                _set_busy(self._m, False)
                if main_thread:
                    stp_py_sigint_target = NULL
                    if old != SIG_ERR:
                        signal(SIGINT, old)
                    if stp_py_sigint_fired:
                        stp_py_sigint_fired = 0
                        PyErr_SetInterrupt()
        finally:
            free(arr)
        PyErr_CheckSignals()
        if self._callback_error is not None:
            e = self._callback_error
            self._callback_error = None
            raise e
        if st != STP_OK:
            self._m._fail("stp_solver_check_sat")
        return (<int>r.kind, <int>r.reason, self._last_reason())

    def entails(self, Term f not None, timeout=None, conflicts=None):
        """(validity, reason, message): validity 1 valid / 2 invalid / 3 unknown."""
        self._live()
        cdef stp_budget budget
        cdef const stp_budget* bp = NULL
        cdef stp_entailment r
        cdef stp_status st
        cdef bint main_thread = 0
        cdef sighandler_t old = SIG_ERR
        if timeout is not None or conflicts is not None:
            budget.has_time = timeout is not None
            budget.time_ms = <uint64_t>(timeout if timeout is not None else 0)
            budget.has_conflicts = conflicts is not None
            budget.conflicts = <uint64_t>(conflicts if conflicts is not None else 0)
            bp = &budget
        self._callback_error = None
        global stp_py_sigint_fired, stp_py_sigint_target
        main_thread = threading.current_thread() is threading.main_thread()
        if main_thread:
            stp_py_sigint_fired = 0
            stp_py_sigint_target = self._s
            old = signal(SIGINT, stp_py_sigint_handler)
        _set_busy(self._m, True)
        try:
            with nogil:
                st = stp_solver_entails(self._s, f._h, bp, &r)
        finally:
            _set_busy(self._m, False)
            if main_thread:
                stp_py_sigint_target = NULL
                if old != SIG_ERR:
                    signal(SIGINT, old)
                if stp_py_sigint_fired:
                    stp_py_sigint_fired = 0
                    PyErr_SetInterrupt()
        PyErr_CheckSignals()
        if self._callback_error is not None:
            e = self._callback_error
            self._callback_error = None
            raise e
        if st != STP_OK:
            self._m._fail("stp_solver_entails")
        return (<int>r.kind, <int>r.reason, self._last_reason())

    def _last_reason(self):
        cdef char* p = stp_solver_last_reason_message(self._s)
        if p == NULL:
            return ""
        return _take(p)

    def unsat_assumptions(self):
        self._live()
        cdef size_t n = stp_solver_num_unsat_assumptions(self._s), i
        cdef stp_term h
        if stp_tm_error(self._m._tm) != NULL:
            self._m._fail("stp_solver_num_unsat_assumptions")
        out = []
        for i in range(n):
            h = stp_solver_unsat_assumption(self._s, i)
            if h == NULL:
                self._m._fail("stp_solver_unsat_assumption")
            out.append(self._m._wrap(h))
        return out

    def model(self):
        self._live()
        cdef stp_model h = stp_solver_model(self._s)
        if h == NULL:
            self._m._fail("stp_solver_model")
        return _wrap_model(self._m, h)

    def candidate_model(self):
        self._live()
        cdef stp_model h = stp_solver_candidate_model(self._s)
        if h == NULL:
            if stp_tm_error(self._m._tm) != NULL:
                self._m._fail("stp_solver_candidate_model")
            return None
        return _wrap_model(self._m, h)

    def value(self, Term t not None):
        self._live()
        cdef stp_term h = stp_solver_value(self._s, t._h)
        if h == NULL:
            self._m._fail("stp_solver_value")
        return self._m._wrap(h)

    # ------------------------------------------------------------ interrupts (any thread)
    def interrupt(self):
        if self._s != NULL:
            stp_solver_interrupt(self._s)

    def clear_interrupt(self):
        if self._s != NULL:
            stp_solver_clear_interrupt(self._s)

    def interrupt_pending(self):
        if self._s == NULL:
            return False
        return bool(stp_solver_interrupt_pending(self._s))

    def set_terminator(self, fn):
        self._live()
        if fn is not None and not callable(fn):
            raise TypeError("the terminator must be callable or None")
        self._terminator = fn
        if fn is None:
            if stp_solver_set_terminator(self._s, NULL, NULL) != STP_OK:
                self._m._fail("stp_solver_set_terminator")
        else:
            if stp_solver_set_terminator(self._s, _terminator_cb, <void*>self._box) != STP_OK:
                self._m._fail("stp_solver_set_terminator")

    def statistics(self):
        self._live()
        cdef stp_statistics h = stp_solver_statistics(self._s)
        if h == NULL:
            self._m._fail("stp_solver_statistics")
        cls = _STATS_CLASS if _STATS_CLASS is not None else StatisticsHandle
        obj = cls.__new__(cls)
        (<StatisticsHandle>obj)._h = h
        (<StatisticsHandle>obj)._m = self._m
        (<StatisticsHandle>obj)._key = <size_t>self._m._tm
        return obj

    # ------------------------------------------------------------ symbols and scripts
    def symbol(self, name):
        self._live()
        cdef bytes b = _b(name)
        cdef stp_term h = stp_solver_symbol(self._s, b)
        if h == NULL:
            if stp_tm_error(self._m._tm) != NULL:
                self._m._fail("stp_solver_symbol")
            return None
        return self._m._wrap(h)

    def parse_smt2(self, text, mode=None):
        self._live()
        cdef bytes b = _b(text)
        cdef const char* p = b
        cdef stp_parse_mode m = STP_PARSE_DECLARE_AND_ASSERT
        if mode is not None:
            m = <stp_parse_mode><int>mode
        cdef stp_status st
        _set_busy(self._m, True)
        try:
            with nogil:
                st = stp_solver_parse_smt2(self._s, p, m)
        finally:
            _set_busy(self._m, False)
        if st != STP_OK:
            self._fail_mutate("stp_solver_parse_smt2")

    def parse_source(self, source, int format, int mode):
        """Parse `source` (a str, bytes, or a readable stream) in any mode."""
        self._live()
        cdef stp_format f = <stp_format>format
        cdef stp_parse_mode m = <stp_parse_mode>mode
        cdef stp_status st
        cdef bytes b
        cdef _TextSource text
        cdef _StreamSource stream = None
        if isinstance(source, (str, bytes)):
            b = _b(source)
            text.data = b
            text.size = len(b)
            text.offset = 0
        else:
            stream = _StreamSource(source)
        _set_busy(self._m, True)
        try:
            if stream is None:
                with nogil:
                    st = stp_solver_parse_source(self._s, _text_source_cb, &text, f, m)
            else:
                with nogil:
                    st = stp_solver_parse_source(self._s, _stream_source_cb, <void*>stream, f, m)
        finally:
            _set_busy(self._m, False)
        if st != STP_OK:
            if stream is not None and stream.error is not None:
                # the stream's own exception says more than the IO error it became
                try:
                    self._fail_mutate("stp_solver_parse_source")
                except Error:
                    pass
                raise stream.error
            self._fail_mutate("stp_solver_parse_source")

    def input_to_string(self, int format):
        self._live()
        cdef char* p = stp_solver_input_to_string(self._s, <stp_format>format)
        if p == NULL:
            self._m._fail("stp_solver_input_to_string")
        return _take(p)

    def parse(self, text, int format):
        self._live()
        cdef bytes b = _b(text)
        cdef const char* p = b
        cdef stp_format f = <stp_format>format
        cdef stp_status st
        _set_busy(self._m, True)
        try:
            with nogil:
                st = stp_solver_parse(self._s, p, f)
        finally:
            _set_busy(self._m, False)
        if st != STP_OK:
            self._fail_mutate("stp_solver_parse")

    def parse_file(self, path, int format):
        self._live()
        cdef bytes b = _b(path)
        cdef const char* p = b
        cdef stp_format f = <stp_format>format
        cdef stp_status st
        _set_busy(self._m, True)
        try:
            with nogil:
                st = stp_solver_parse_file(self._s, p, f)
        finally:
            _set_busy(self._m, False)
        if st != STP_OK:
            self._fail_mutate("stp_solver_parse_file")

    def parse_term(self, text):
        self._live()
        cdef bytes b = _b(text)
        cdef stp_term h = stp_solver_parse_term(self._s, b)
        if h == NULL:
            self._fail_mutate("stp_solver_parse_term")
        return self._m._wrap(h)

    def to_smt2(self, with_check_sat=False):
        self._live()
        cdef char* p = stp_solver_to_smt2(self._s, 1 if with_check_sat else 0)
        if p == NULL:
            self._m._fail("stp_solver_to_smt2")
        return _take(p)

    def to_string(self, int format):
        self._live()
        cdef char* p = stp_solver_to_string(self._s, <stp_format>format)
        if p == NULL:
            self._m._fail("stp_solver_to_string")
        return _take(p)

    def write_cnf(self):
        """The DIMACS text of the assertions (encoded up to CNF without solving), as bytes."""
        self._live()
        cdef list chunks = []
        cdef void* user = <void*>chunks
        cdef stp_status st
        _set_busy(self._m, True)
        try:
            with nogil:
                st = stp_solver_write_cnf(self._s, _collect_cb, user)
        finally:
            _set_busy(self._m, False)
        if st != STP_OK:
            self._m._fail("stp_solver_write_cnf")
        return b"".join(chunks)

    def set_diagnostic_sink(self, fn):
        self._live()
        if fn is not None and not callable(fn):
            raise TypeError("the diagnostic sink must be callable or None")
        self._sink = fn
        if fn is None:
            stp_solver_set_diagnostic_sink(self._s, NULL, NULL)
        else:
            stp_solver_set_diagnostic_sink(self._s, _sink_cb, <void*>self._box)

    def set_output_sink(self, fn):
        self._live()
        if fn is not None and not callable(fn):
            raise TypeError("the output sink must be callable or None")
        self._out_sink = fn
        if fn is None:
            stp_solver_set_output_sink(self._s, NULL, NULL)
        else:
            stp_solver_set_output_sink(self._s, _out_sink_cb, <void*>self._box)

    def set_fatal_error_handler(self, fn):
        self._live()
        if fn is not None and not callable(fn):
            raise TypeError("the fatal error handler must be callable or None")
        self._fatal_handler = fn
        if fn is None:
            stp_solver_set_fatal_error_handler(self._s, NULL, NULL)
        else:
            stp_solver_set_fatal_error_handler(self._s, _fatal_cb, <void*>self._box)

    def set_cnf_sink(self, fn):
        self._live()
        if fn is not None and not callable(fn):
            raise TypeError("the CNF sink must be callable or None")
        self._cnf_sink = fn
        if fn is None:
            stp_solver_set_cnf_sink(self._s, NULL, NULL)
        else:
            stp_solver_set_cnf_sink(self._s, _cnf_cb, <void*>self._box)


# ----------------------------------------------------------------- Model

cdef object _wrap_model(Manager m, stp_model h):
    cls = _MODEL_CLASS if _MODEL_CLASS is not None else ModelHandle
    obj = cls.__new__(cls)
    (<ModelHandle>obj)._h = h
    (<ModelHandle>obj)._m = m
    (<ModelHandle>obj)._key = <size_t>m._tm
    return obj


cdef class ModelHandle:
    """A detached model snapshot (stp_model)."""

    def __cinit__(self, *args, **kwargs):
        self._h = NULL
        self._m = None

    def __dealloc__(self):
        cdef Manager m
        if self._h != NULL:
            m = self._m
            if m is not None and not m._busy:
                stp_model_release(self._h)
            else:
                _defer(self._key, DEFER_MODEL, <void*>self._h)
            self._h = NULL

    def _manager(self):
        return self._m

    def copy(self):
        self._m._check()
        cdef stp_model h = stp_model_copy(self._h)
        if h == NULL:
            self._m._fail("stp_model_copy")
        return _wrap_model(self._m, h)

    def value(self, Term t not None):
        """The value of t, completing symbols outside the core."""
        self._m._check()
        cdef stp_term h = stp_model_value(self._h, t._h)
        if h == NULL:
            self._m._fail("stp_model_value")
        return self._m._wrap(h)

    def try_value(self, Term t not None):
        """The value of t, or None if completion would be needed."""
        self._m._check()
        cdef stp_term h = stp_model_try_value(self._h, t._h)
        if h == NULL:
            if stp_tm_error(self._m._tm) != NULL:
                self._m._fail("stp_model_try_value")
            return None
        return self._m._wrap(h)

    def values(self, list ts not None):
        self._m._check()
        cdef size_t n = 0, i
        cdef stp_term* arr = self._m._array(ts, &n, "stp_model_values")
        cdef stp_term* out = <stp_term*>malloc((n if n > 0 else 1) * sizeof(stp_term))
        if out == NULL:
            free(arr)
            raise MemoryError()
        try:
            if stp_model_values(self._h, n, arr, out) != STP_OK:
                self._m._fail("stp_model_values")
            res = []
            for i in range(n):
                res.append(self._m._wrap(out[i]))
            return res
        finally:
            free(arr)
            free(out)

    def array_value(self, Term t not None):
        self._m._check()
        cdef stp_array_value h = stp_model_array_value(self._h, t._h)
        if h == NULL:
            self._m._fail("stp_model_array_value")
        cls = _ARRAY_VALUE_CLASS if _ARRAY_VALUE_CLASS is not None else ArrayValueHandle
        obj = cls.__new__(cls)
        (<ArrayValueHandle>obj)._h = h
        (<ArrayValueHandle>obj)._m = self._m
        (<ArrayValueHandle>obj)._key = <size_t>self._m._tm
        return obj

    def fun_value(self, Term t not None):
        self._m._check()
        cdef stp_fun_value h = stp_model_fun_value(self._h, t._h)
        if h == NULL:
            self._m._fail("stp_model_fun_value")
        cls = _FUN_VALUE_CLASS if _FUN_VALUE_CLASS is not None else FunValueHandle
        obj = cls.__new__(cls)
        (<FunValueHandle>obj)._h = h
        (<FunValueHandle>obj)._m = self._m
        (<FunValueHandle>obj)._key = <size_t>self._m._tm
        return obj

    def array_bytes(self, Term t not None, first_index, count):
        """count elements from first_index of a BV-indexed array of byte-multiple elements."""
        self._m._check()
        cdef stp_sort s = stp_term_sort(t._h)
        cdef stp_sort e
        cdef uint32_t w = 0
        cdef size_t n = <size_t>count
        if s != NULL:
            e = stp_sort_array_element(s)
            if e != NULL and stp_sort_bv_size(e, &w) != STP_OK:
                stp_tm_clear_error(self._m._tm)
                w = 0
        if w == 0 or w % 8 != 0:
            raise ArgumentError("array_bytes needs a BV-indexed array whose element width is a multiple of 8",
                                code=ErrorCode.INVALID_ARGUMENT, function="stp_model_array_bytes")
        # A bytes object holds at most sys.maxsize bytes. Past that the size_t
        # product below wraps, and the call would write beyond the allocation.
        if count * (w // 8) > sys.maxsize:
            raise DoesNotFit("array_bytes: %d elements of %d bytes do not fit a bytes object" % (count, w // 8),
                             code=ErrorCode.DOES_NOT_FIT, function="stp_model_array_bytes")
        cdef bytes out = PyBytes_FromStringAndSize(NULL, n * (w // 8))
        if stp_model_array_bytes(self._h, t._h, <uint64_t>first_index, n, <uint8_t*><char*>out) != STP_OK:
            self._m._fail("stp_model_array_bytes")
        return out

    def num_symbols(self):
        return stp_model_num_symbols(self._h)

    def symbol(self, i):
        self._m._check()
        cdef stp_term h = stp_model_symbol(self._h, <size_t>i)
        if h == NULL:
            self._m._fail("stp_model_symbol")
        return self._m._wrap(h)

    def symbols(self):
        self._m._check()
        cdef size_t n = stp_model_num_symbols(self._h), i
        cdef stp_term h
        out = []
        for i in range(n):
            h = stp_model_symbol(self._h, i)
            if h == NULL:
                self._m._fail("stp_model_symbol")
            out.append(self._m._wrap(h))
        return out

    def in_core(self, Term t not None):
        self._m._check()
        return bool(stp_model_in_core(self._h, t._h))

    def to_smt2(self):
        self._m._check()
        cdef char* p = stp_model_to_smt2(self._h)
        if p == NULL:
            self._m._fail("stp_model_to_smt2")
        return _take(p)


cdef class ArrayValueHandle:
    """The value of an array in a model: default + explicit entries (stp_array_value)."""

    def __cinit__(self, *args, **kwargs):
        self._h = NULL
        self._m = None

    def __dealloc__(self):
        cdef Manager m
        if self._h != NULL:
            m = self._m
            if m is not None and not m._busy:
                stp_array_value_release(self._h)
            else:
                _defer(self._key, DEFER_ARRAY, <void*>self._h)
            self._h = NULL

    def _manager(self):
        return self._m

    def sort(self):
        cdef stp_sort h = stp_array_value_sort(self._h)
        if h == NULL:
            self._m._fail("stp_array_value_sort")
        return self._m._wrap_sort(h)

    def default_value(self):
        self._m._check()
        cdef stp_term h = stp_array_value_default(self._h)
        if h == NULL:
            self._m._fail("stp_array_value_default")
        return self._m._wrap(h)

    def size(self):
        return stp_array_value_size(self._h)

    def entry(self, i):
        """(index, element)"""
        self._m._check()
        cdef stp_term idx = NULL, el = NULL
        cdef size_t n = stp_array_value_size(self._h)
        if not isinstance(i, int) or i < 0 or <size_t>i >= n:
            raise IndexError("entry %r out of range for an array value with %d entries" % (i, n))
        if stp_array_value_entry(self._h, <size_t>i, &idx, &el) != STP_OK:
            self._m._fail("stp_array_value_entry")
        return (self._m._wrap(idx), self._m._wrap(el))

    def at(self, Term index_value not None):
        self._m._check()
        cdef stp_term h = stp_array_value_at(self._h, index_value._h)
        if h == NULL:
            self._m._fail("stp_array_value_at")
        return self._m._wrap(h)

    def as_term(self):
        self._m._check()
        cdef stp_term h = stp_array_value_as_term(self._h)
        if h == NULL:
            self._m._fail("stp_array_value_as_term")
        return self._m._wrap(h)


cdef class FunValueHandle:
    """The value of a function symbol in a model (stp_fun_value)."""

    def __cinit__(self, *args, **kwargs):
        self._h = NULL
        self._m = None

    def __dealloc__(self):
        cdef Manager m
        if self._h != NULL:
            m = self._m
            if m is not None and not m._busy:
                stp_fun_value_release(self._h)
            else:
                _defer(self._key, DEFER_FUN, <void*>self._h)
            self._h = NULL

    def _manager(self):
        return self._m

    def sort(self):
        cdef stp_sort h = stp_fun_value_sort(self._h)
        if h == NULL:
            self._m._fail("stp_fun_value_sort")
        return self._m._wrap_sort(h)

    def arity(self):
        return stp_fun_value_arity(self._h)

    def else_value(self):
        self._m._check()
        cdef stp_term h = stp_fun_value_else(self._h)
        if h == NULL:
            self._m._fail("stp_fun_value_else")
        return self._m._wrap(h)

    def size(self):
        return stp_fun_value_size(self._h)

    def entry(self, i):
        """((arg values...), value)"""
        self._m._check()
        cdef size_t n = stp_fun_value_size(self._h), k
        cdef uint32_t arity = stp_fun_value_arity(self._h)
        cdef stp_term* args
        cdef stp_term val = NULL
        if not isinstance(i, int) or i < 0 or <size_t>i >= n:
            raise IndexError("entry %r out of range for a function value with %d entries" % (i, n))
        args = <stp_term*>malloc((arity if arity > 0 else 1) * sizeof(stp_term))
        if args == NULL:
            raise MemoryError()
        try:
            if stp_fun_value_entry(self._h, <size_t>i, args, &val) != STP_OK:
                self._m._fail("stp_fun_value_entry")
            avs = tuple(self._m._wrap(args[k]) for k in range(arity))
        finally:
            free(args)
        return (avs, self._m._wrap(val))

    def apply(self, list arg_values not None):
        self._m._check()
        cdef size_t n = 0
        cdef stp_term* arr = self._m._array(arg_values, &n, "stp_fun_value_apply")
        cdef stp_term h
        try:
            h = stp_fun_value_apply(self._h, n, arr)
        finally:
            free(arr)
        if h == NULL:
            self._m._fail("stp_fun_value_apply")
        return self._m._wrap(h)

    def as_ite(self, list formals not None):
        self._m._check()
        cdef size_t n = 0
        cdef stp_term* arr = self._m._array(formals, &n, "stp_fun_value_as_ite")
        cdef stp_term h
        try:
            h = stp_fun_value_as_ite(self._h, n, arr)
        finally:
            free(arr)
        if h == NULL:
            self._m._fail("stp_fun_value_as_ite")
        return self._m._wrap(h)


cdef int _fail_stats(Manager m, const char* fn) except -1:
    """A statistics handle has no manager in the C layer: its errors land in the thread-local
    record; the manager's record is checked first in case the layer changes."""
    cdef const stp_error* e = stp_tm_error(m._tm) if m is not None else NULL
    if e != NULL:
        m._fail(fn)
    _raise_thread_local(fn)
    return 0


cdef class StatisticsHandle:
    """A statistics snapshot (stp_statistics), keyed by the names of statistics.toml."""

    def __cinit__(self, *args, **kwargs):
        self._h = NULL
        self._m = None

    def __dealloc__(self):
        cdef Manager m
        if self._h != NULL:
            m = self._m
            if m is not None and not m._busy:
                stp_statistics_release(self._h)
            else:
                _defer(self._key, DEFER_STATS, <void*>self._h)
            self._h = NULL

    def size(self):
        return stp_statistics_size(self._h)

    def names(self):
        cdef size_t n = stp_statistics_size(self._h), i
        cdef const char* p
        out = []
        for i in range(n):
            p = stp_statistics_name(self._h, i)
            if p != NULL:
                out.append(_s(p))
        return out

    def is_uint64(self, name):
        cdef bytes b = _b(name)
        return bool(stp_statistics_is_uint64(self._h, b))

    def is_double(self, name):
        cdef bytes b = _b(name)
        return bool(stp_statistics_is_double(self._h, b))

    def get_uint64(self, name):
        cdef bytes b = _b(name)
        cdef uint64_t v
        if stp_statistics_uint64(self._h, b, &v) != STP_OK:
            _fail_stats(self._m, "stp_statistics_uint64")
        return v

    def get_double(self, name):
        cdef bytes b = _b(name)
        cdef double v
        if stp_statistics_double(self._h, b, &v) != STP_OK:
            _fail_stats(self._m, "stp_statistics_double")
        return v

    def get_str(self, name):
        cdef bytes b = _b(name)
        cdef char* p = stp_statistics_str(self._h, b)
        if p == NULL:
            _fail_stats(self._m, "stp_statistics_str")
        return _take(p)


def statistics_tier(name):
    """The tier of a statistic name (ArgumentError for an unknown name)."""
    cdef bytes b = _b(name)
    cdef stp_tier t
    cdef const stp_error* e
    # An unknown name answers STABLE and records INVALID_ARGUMENT in the thread-local record,
    # which nothing clears on success: plant a sentinel error first, so that a record that
    # still shows the sentinel afterwards means the call succeeded.
    stp_option_info_type(b"\x01stp-python-sentinel\x01")
    t = stp_statistics_tier(b)
    e = stp_last_error()
    if e != NULL and e.code == STP_ERR_INVALID_ARGUMENT:
        raise _exc_from(e, None, False)
    return <int>t


# ----------------------------------------------------------------- library

def version():
    """(major, minor, patch, string, git_sha, git_tag, build_info)"""
    cdef stp_version v = stp_get_version()
    return (v.major, v.minor, v.patch, _s(v.string) or "", _s(v.git_sha) or "", _s(v.git_tag) or "",
            _s(v.build_info) or "")


def capability(key):
    cdef bytes b = _b(key)
    return _take(stp_capability(b))


def capabilities():
    """The raw "key=value\\n..." text."""
    return _take(stp_capabilities()) or ""


def has_sat_backend(name):
    cdef bytes b = _b(name)
    return bool(stp_has_sat_backend(b))


def sat_backends():
    cdef size_t n = stp_num_sat_backends(), i
    return [_s(stp_sat_backend_name(i)) for i in range(n)]


def kind_name(int k):
    return _s(stp_kind_name(<stp_kind>k))


def kind_smtlib(int k):
    return _s(stp_kind_smtlib(<stp_kind>k))


def rm_name(int rm):
    return _s(stp_rm_name(<stp_rm>rm))


def unknown_reason_name(int r):
    return _s(stp_unknown_reason_name(<stp_unknown_reason>r))


def error_code_name(int c):
    return _s(stp_error_code_name(<stp_error_code>c))


def result_kind_name(int k):
    return _s(stp_result_kind_name(<stp_result_kind>k))


def validity_name(int v):
    return _s(stp_validity_name(<stp_validity>v))


def set_internal_error_policy(abort):
    stp_set_internal_error_policy(STP_ABORT if abort else STP_POISON)


def get_internal_error_policy():
    return stp_get_internal_error_policy() == STP_ABORT


def last_error():
    """The thread-local record as an exception object, or None (diagnostics)."""
    cdef const stp_error* e = stp_last_error()
    if e == NULL:
        return None
    return _exc_from(e, None, False)


# constants the shell reads (so that it never hard-codes the C values)
SORT_BOOL = <int>STP_SORT_BOOL
SORT_BV = <int>STP_SORT_BV
SORT_FP = <int>STP_SORT_FP
SORT_RM = <int>STP_SORT_RM
SORT_REAL = <int>STP_SORT_REAL
SORT_ARRAY = <int>STP_SORT_ARRAY
SORT_FUN = <int>STP_SORT_FUN
SORT_UNINTERPRETED = <int>STP_SORT_UNINTERPRETED
RM_RNE = <int>STP_RM_RNE
RM_RNA = <int>STP_RM_RNA
RM_RTP = <int>STP_RM_RTP
RM_RTN = <int>STP_RM_RTN
RM_RTZ = <int>STP_RM_RTZ
RESULT_SAT = <int>STP_SAT
RESULT_UNSAT = <int>STP_UNSAT
RESULT_UNKNOWN = <int>STP_UNKNOWN
VALIDITY_VALID = <int>STP_VALID
VALIDITY_INVALID = <int>STP_INVALID
VALIDITY_UNKNOWN = <int>STP_UNKNOWN_VALIDITY
FORMAT_AUTO = <int>STP_FORMAT_AUTO
FORMAT_SMTLIB2 = <int>STP_FORMAT_SMTLIB2
FORMAT_SMTLIB1 = <int>STP_FORMAT_SMTLIB1
FORMAT_CVC = <int>STP_FORMAT_CVC
FORMAT_DOT = <int>STP_FORMAT_DOT
FORMAT_GDL = <int>STP_FORMAT_GDL
PARSE_DECLARE_AND_ASSERT = <int>STP_PARSE_DECLARE_AND_ASSERT
PARSE_EXECUTE = <int>STP_PARSE_EXECUTE
PARSE_ONLY = <int>STP_PARSE_ONLY
FP_NORMAL = <int>STP_FP_NORMAL
FP_SUBNORMAL = <int>STP_FP_SUBNORMAL
FP_ZERO = <int>STP_FP_ZERO
FP_INFINITY = <int>STP_FP_INFINITY
FP_NAN = <int>STP_FP_NAN
TIER_STABLE = <int>STP_TIER_STABLE
TIER_EXPERT = <int>STP_TIER_EXPERT
TIER_EXPERIMENTAL = <int>STP_TIER_EXPERIMENTAL
TIER_DIAGNOSTIC = <int>STP_TIER_DIAGNOSTIC
SETTABLE_ANYTIME = <int>STP_SETTABLE_ANYTIME
SETTABLE_BEFORE_FIRST_CHECK = <int>STP_SETTABLE_BEFORE_FIRST_CHECK
SETTABLE_CONSTRUCTION = <int>STP_SETTABLE_CONSTRUCTION
SCOPE_SOLVER = <int>STP_SCOPE_SOLVER
SCOPE_MANAGER = <int>STP_SCOPE_MANAGER
