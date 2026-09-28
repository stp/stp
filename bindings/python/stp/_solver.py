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

"""The solver layer of the STP 3.x Python API: Options, the results, Statistics, Solver,
Model and the z3py-style conveniences (SolverFor, solve, prove, the @stp decorator)."""

import ast
import collections.abc
import contextlib
import datetime
import inspect
import io
import os
import sys
import threading
import weakref

from . import _core
from ._core import (Error, ArgumentError, SortMismatch, NotAValue, NoModel, Unsupported, OptionError,
                    UnknownOption, ParseError, StateError)
from ._gen_kinds import Kind, ErrorCode, Option
from ._terms import (TermManager, main_tm, _tm, SortKind, RoundingMode, UnknownReason, Tier, _reason,
                     ExprRef, BoolRef, BitVecRef, ArrayRef, ArrayNumRef, FuncRef, FuncInterp, SortRef,
                     _coerce_arg, _flatten_bools, _format_code, _is_int, BitVec, Not, And, BoolVal)

_PARSE_MODES = {
    "declare-and-assert": _core.PARSE_DECLARE_AND_ASSERT,
    "execute": _core.PARSE_EXECUTE,
    "parse-only": _core.PARSE_ONLY,
}


def _parse_mode(name):
    try:
        return _PARSE_MODES[str(name).lower()]
    except KeyError:
        raise ArgumentError("unknown parse mode %r; expected one of %s" % (name, ", ".join(sorted(_PARSE_MODES))),
                            code=ErrorCode.INVALID_ARGUMENT) from None


# ---------------------------------------------------------------- options

_SETTABLE_NAMES = {
    _core.SETTABLE_ANYTIME: "anytime",
    _core.SETTABLE_BEFORE_FIRST_CHECK: "before-first-check",
    _core.SETTABLE_CONSTRUCTION: "construction",
}
_SCOPE_NAMES = {_core.SCOPE_SOLVER: "solver", _core.SCOPE_MANAGER: "manager"}

_registry = None
_registry_lock = threading.Lock()


def _keys():
    """{name | python_key | alias: registry name} for every option (built once)."""
    global _registry
    if _registry is None:
        with _registry_lock:
            if _registry is None:
                reg = {}
                for name in _core.option_names(-1):
                    info = _core.option_info(name)
                    reg.setdefault(name, name)
                    reg.setdefault(info["python_key"], name)
                    reg.setdefault(name.replace("-", "_").replace(".", "_"), name)
                    for alias in info["aliases"]:
                        reg.setdefault(alias, name)
                        reg.setdefault(alias.replace("-", "_").replace(".", "_"), name)
                reg.setdefault("timeout", "max-time")  # z3py's spelling
                _registry = reg
    return _registry


def _canonical(key):
    if not isinstance(key, str):
        raise TypeError("an option key is a str, got %s" % type(key).__name__)
    reg = _keys()
    name = reg.get(key)
    if name is None:
        raise UnknownOption("unknown option '%s'" % key, code=ErrorCode.OPTION_UNKNOWN, option=key,
                            function="Options")
    return name


def _typed_text(type_, text):
    """A registry text value (default / current) as a Python value."""
    if text is None:
        return None
    if type_ == "bool":
        return text.lower() in ("true", "1", "on", "yes")
    if type_ in ("int", "uint"):
        try:
            return int(text)
        except ValueError:
            return text
    if type_ == "duration":
        return None if text in ("none", "") else _duration_ms(text)
    if type_ == "set":
        return [] if text in ("", "none") else text.split(",")
    return text


_DURATION_UNITS = {"ms": 1, "s": 1000, "m": 60000, "h": 3600000}


def _duration_ms(text):
    import re
    m = re.match(r"^\s*([0-9]*\.?[0-9]+)\s*(ms|s|m|h)?\s*$", text)
    if not m:
        return text
    v = float(m.group(1)) * _DURATION_UNITS.get(m.group(2) or "s", 1000)
    return int(round(v))


class _LiveBackend:
    """The live options of a solver, with the same method names as a standalone
    OptionsHandle. It calls the core's methods explicitly: the Solver subclass overrides
    set_args, reset and others with the solver-level meanings. The solver is held weakly:
    the solver caches this view, and a strong reference back made every solver whose
    options were touched cyclic garbage, freed only by the collector."""

    __slots__ = ("_ref",)

    def __init__(self, solver):
        self._ref = weakref.ref(solver)

    @property
    def _s(self):
        solver = self._ref()
        if solver is None:
            raise _core.StateError("the solver is gone")
        return solver

    def set_str(self, n, v):
        return _core.SolverHandle.set_str(self._s, n, v)

    def set_bool(self, n, v):
        return _core.SolverHandle.set_bool(self._s, n, v)

    def set_int64(self, n, v):
        return _core.SolverHandle.set_int64(self._s, n, v)

    def set_uint64(self, n, v):
        return _core.SolverHandle.set_uint64(self._s, n, v)

    def set_duration_ms(self, n, v):
        return _core.SolverHandle.set_duration_ms(self._s, n, v)

    def set_names(self, n, v):
        return _core.SolverHandle.set_names(self._s, n, v)

    def set_args(self, argv):
        return _core.SolverHandle.set_args(self._s, argv)

    def get_str(self, n):
        return _core.SolverHandle.get_str(self._s, n)

    def get_bool(self, n):
        return _core.SolverHandle.get_bool(self._s, n)

    def get_int64(self, n):
        return _core.SolverHandle.get_int64(self._s, n)

    def get_uint64(self, n):
        return _core.SolverHandle.get_uint64(self._s, n)

    def get_duration_ms(self, n):
        return _core.SolverHandle.get_duration_ms(self._s, n)

    def resolved_str(self, n):
        return _core.SolverHandle.resolved_str(self._s, n)

    def is_set(self, n):
        return _core.SolverHandle.is_set(self._s, n)

    def reset(self, n):
        return _core.SolverHandle.reset_option(self._s, n)

    def options_copy(self):
        return _core.SolverHandle.options_copy(self._s)


class OptionInfo:
    """Everything the registry knows about one option, plus its current value in the
    Options object that produced it."""

    def __init__(self, info, current=None, resolved=None, is_set=False):
        self.name = info["name"]
        self.python_key = info["python_key"]
        self.type = info["type"]
        self.default = _typed_text(info["type"], info["default"])
        self.current = current
        self.resolved = resolved
        self.min = info["min"]
        self.max = info["max"]
        self.values = list(info["values"])
        self.tier = Tier(info["tier"])
        self.settable = _SETTABLE_NAMES.get(info["settable"], str(info["settable"]))
        self.scope = _SCOPE_NAMES.get(info["scope"], str(info["scope"]))
        self.category = info["category"]
        self.help = info["help"]
        self.supported = info["supported"]
        self.is_set = is_set
        self.aliases = list(info["aliases"])
        self.short = info["short"]
        self.negation = info["negation"]

    def __repr__(self):
        return "OptionInfo(%s: %s, default=%r, current=%r, tier=%s, settable=%s, scope=%s)" % (
            self.name, self.type, self.default, self.current, self.tier.name, self.settable, self.scope)


class Options:
    """Mapping-like access to the registry. A key is the registry name or its python_key ('-'
    and '.' become '_'; `timeout` is an alias of `max_time`). Values are validated at write
    time; durations take an int of milliseconds, a timedelta, or a string with a unit ("500ms",
    "0.5s"); a mode option takes True/False or "auto"/"on"/"off"; a set option a list of names.

    Options(**kwargs) is a standalone value; Solver.options is the live view of a solver, where
    the entry's Settable window is enforced."""

    def __init__(self, *positional_pairs, **kwargs):
        self._handle = _core.OptionsHandle()
        self._solver = None
        self.set(*positional_pairs, **kwargs)

    @classmethod
    def _live(cls, solver):
        obj = cls.__new__(cls)
        obj._handle = None
        obj._solver = _LiveBackend(solver)
        return obj

    @classmethod
    def _wrap(cls, handle):
        obj = cls.__new__(cls)
        obj._handle = handle
        obj._solver = None
        return obj

    @property
    def _backend(self):
        if self._solver is not None:
            return self._solver
        return self._handle

    @property
    def live(self):
        """True for a solver's live view."""
        return self._solver is not None

    # ------------------------------------------------------------ writing
    def _write(self, name, value):
        b = self._backend
        info = _core.option_info(name)
        type_ = info["type"]
        if isinstance(value, RoundingMode):
            b.set_str(name, value.name)
        elif isinstance(value, bool):
            if type_ == "mode":
                b.set_str(name, "on" if value else "off")
            else:
                b.set_bool(name, value)
        elif isinstance(value, int):
            if type_ == "duration":
                if value < 0:
                    raise OptionError("option '%s': a duration cannot be negative (%d)" % (name, value),
                                      code=ErrorCode.OPTION_VALUE, option=name)
                b.set_duration_ms(name, value)
            elif type_ == "uint":
                if value < 0:
                    raise OptionError("option '%s': expected a non-negative int, got %d" % (name, value),
                                      code=ErrorCode.OPTION_VALUE, option=name)
                b.set_uint64(name, value)
            else:
                b.set_int64(name, value)
        elif isinstance(value, float):
            if type_ == "duration":
                b.set_duration_ms(name, int(round(value)))
            else:
                raise OptionError("option '%s' (%s) cannot take a float" % (name, type_),
                                  code=ErrorCode.OPTION_VALUE, option=name)
        elif isinstance(value, datetime.timedelta):
            b.set_duration_ms(name, int(round(value.total_seconds() * 1000)))
        elif isinstance(value, str):
            b.set_str(name, value)
        elif value is None:
            if type_ == "duration":
                b.set_str(name, "none")
            else:
                raise OptionError("option '%s' (%s) cannot take None" % (name, type_),
                                  code=ErrorCode.OPTION_VALUE, option=name)
        elif isinstance(value, (list, tuple, set, frozenset)):
            b.set_names(name, [str(v) for v in value])
        else:
            raise OptionError("option '%s' (%s) cannot take a %s" % (name, type_, type(value).__name__),
                              code=ErrorCode.OPTION_VALUE, option=name)

    def __setitem__(self, key, value):
        self._write(_canonical(key), value)

    def set(self, *positional_pairs, **kwargs):
        """set("max-time", 500) / set("max-time", 500, "random-seed", 7) / set(max_time=500) /
        set({"max-time": 500}); z3py's timeout= is an alias of max_time."""
        if len(positional_pairs) == 1 and isinstance(positional_pairs[0], dict):
            for k, v in positional_pairs[0].items():
                self[k] = v
        elif positional_pairs:
            if len(positional_pairs) % 2 != 0:
                raise TypeError("set() takes name, value pairs")
            for i in range(0, len(positional_pairs), 2):
                self[positional_pairs[i]] = positional_pairs[i + 1]
        for k, v in kwargs.items():
            self[k] = v

    def set_args(self, *argv):
        """CLI syntax: "--fp-abstraction", "--max-time=500ms" (durations need a unit here)."""
        if len(argv) == 1 and isinstance(argv[0], (list, tuple)):
            argv = tuple(argv[0])
        self._backend.set_args([str(a) for a in argv])

    def reset(self, name=None):
        if name is None:
            if self._solver is not None:
                for n in _core.option_names(-1):
                    if self._solver.is_set(n):
                        self._solver.reset(n)  # _LiveBackend.reset: the option reset
            else:
                self._handle.reset_all()
        else:
            self._backend.reset(_canonical(name))

    # ------------------------------------------------------------ reading
    def _read(self, name):
        b = self._backend
        type_ = _core.option_info(name)["type"]
        if type_ == "bool":
            return b.get_bool(name)
        if type_ == "int":
            return b.get_int64(name)
        if type_ == "uint":
            return b.get_uint64(name)
        if type_ == "duration":
            if b.get_str(name) == "none":
                return None
            return b.get_duration_ms(name)
        if type_ == "set":
            s = b.get_str(name)
            return [] if s in ("", "none") else s.split(",")
        return b.get_str(name)

    def __getitem__(self, key):
        return self._read(_canonical(key))

    def get(self, name, default=None):
        try:
            return self[name]
        except UnknownOption:
            return default

    def resolved(self, name):
        name = _canonical(name)
        return _typed_text(_core.option_info(name)["type"], self._backend.resolved_str(name))

    def is_set(self, name):
        return self._backend.is_set(_canonical(name))

    def __contains__(self, key):
        try:
            _canonical(key)
            return True
        except (UnknownOption, TypeError):
            return False

    def __iter__(self):
        return iter(_core.option_names(-1))

    def __len__(self):
        return len(_core.option_names(-1))

    def keys(self):
        return list(_core.option_names(-1))

    def items(self):
        return [(n, self._read(n)) for n in _core.option_names(-1)]

    def info(self, name):
        name = _canonical(name)
        info = _core.option_info(name)
        b = self._backend
        try:
            current = self._read(name)
        except Error:
            current = None
        try:
            resolved = _typed_text(info["type"], b.resolved_str(name))
        except Error:
            resolved = None
        try:
            is_set = b.is_set(name)
        except Error:
            is_set = False
        return OptionInfo(info, current, resolved, is_set)

    @staticmethod
    def names(tier=None):
        return _core.option_names(-1 if tier is None else int(tier))

    @staticmethod
    def help(tier=None):
        return _core.option_help(-1 if tier is None else int(tier))

    def resolve(self):
        if self._solver is not None:
            return  # a solver's options are resolved at construction
        self._handle.resolve()

    def copy(self):
        if self._solver is not None:
            return Options._wrap(self._solver.options_copy())
        return Options._wrap(self._handle.copy())

    def _set_entries(self):
        out = {}
        for n in _core.option_names(-1):
            try:
                if self._backend.is_set(n):
                    out[n] = self._read(n)
            except Error:
                pass
        return out

    def __repr__(self):
        entries = self._set_entries()
        body = ", ".join("%s=%r" % (_core.option_info(n)["python_key"], v) for n, v in entries.items())
        return "Options(%s)" % body

    def __eq__(self, other):
        if not isinstance(other, Options):
            return NotImplemented
        return self._set_entries() == other._set_entries()

    __hash__ = None


# ---------------------------------------------------------------- results


class CheckSatResult:
    """sat, unsat or unknown, with the reason attached. Hashable; bool(r) raises TypeError:
    compare with sat/unsat/unknown."""

    __slots__ = ("_kind", "_reason", "_message")

    def __init__(self, kind, reason=0, message=""):
        self._kind = int(kind)
        self._reason = int(reason)
        self._message = message or ""

    @property
    def reason(self):
        return _reason(self._reason)

    @property
    def reason_message(self):
        return self._message

    def is_sat(self):
        return self._kind == _core.RESULT_SAT

    def is_unsat(self):
        return self._kind == _core.RESULT_UNSAT

    def is_unknown(self):
        return self._kind == _core.RESULT_UNKNOWN

    def __eq__(self, other):
        if isinstance(other, CheckSatResult):
            return self._kind == other._kind
        if isinstance(other, EntailmentResult):
            return self.is_unknown() and other.is_unknown()
        return NotImplemented

    def __ne__(self, other):
        r = self.__eq__(other)
        return r if r is NotImplemented else not r

    def __hash__(self):
        return hash(("CheckSatResult", self._kind))

    def __bool__(self):
        raise TypeError("a check result has no truth value: compare it with sat, unsat or unknown")

    def __repr__(self):
        name = _core.result_kind_name(self._kind)
        if self.is_unknown() and self._reason != 0:
            return "%s (%s)" % (name, self.reason.value)
        return name

    __str__ = __repr__


sat = CheckSatResult(_core.RESULT_SAT)
unsat = CheckSatResult(_core.RESULT_UNSAT)
unknown = CheckSatResult(_core.RESULT_UNKNOWN)


class EntailmentResult:
    """valid, invalid or unknown, with the reason attached."""

    __slots__ = ("_kind", "_reason", "_message")

    def __init__(self, kind, reason=0, message=""):
        self._kind = int(kind)
        self._reason = int(reason)
        self._message = message or ""

    @property
    def reason(self):
        return _reason(self._reason)

    @property
    def reason_message(self):
        return self._message

    def is_valid(self):
        return self._kind == _core.VALIDITY_VALID

    def is_invalid(self):
        return self._kind == _core.VALIDITY_INVALID

    def is_unknown(self):
        return self._kind == _core.VALIDITY_UNKNOWN

    def __eq__(self, other):
        if isinstance(other, EntailmentResult):
            return self._kind == other._kind
        if isinstance(other, CheckSatResult):
            return self.is_unknown() and other.is_unknown()
        return NotImplemented

    def __ne__(self, other):
        r = self.__eq__(other)
        return r if r is NotImplemented else not r

    def __hash__(self):
        return hash(("EntailmentResult", self._kind))

    def __bool__(self):
        raise TypeError("an entailment result has no truth value: compare it with valid, invalid or unknown")

    def __repr__(self):
        name = _core.validity_name(self._kind)
        if self.is_unknown() and self._reason != 0:
            return "%s (%s)" % (name, self.reason.value)
        return name

    __str__ = __repr__


valid = EntailmentResult(_core.VALIDITY_VALID)
invalid = EntailmentResult(_core.VALIDITY_INVALID)


# ---------------------------------------------------------------- statistics


class Statistics(_core.StatisticsHandle):
    """A snapshot of the solver's statistics, keyed by the names of statistics.toml
    (a read-only mapping: int, float or str values)."""

    def __getitem__(self, name):
        if not isinstance(name, str):
            raise TypeError("a statistic name is a str")
        try:
            if self.is_uint64(name):
                return self.get_uint64(name)
            if self.is_double(name):
                return self.get_double(name)
            return self.get_str(name)
        except ArgumentError:
            raise KeyError(name) from None

    def __iter__(self):
        return iter(self.names())

    def __len__(self):
        return self.size()

    def __contains__(self, name):
        return isinstance(name, str) and name in self.names()

    def keys(self):
        return self.names()

    def items(self):
        return [(n, self[n]) for n in self.names()]

    def values(self):
        return [self[n] for n in self.names()]

    def get(self, name, default=None):
        try:
            return self[name]
        except KeyError:
            return default

    def tier(self, name):
        return Tier(_core.statistics_tier(name))

    def __repr__(self):
        return "Statistics(%s)" % ", ".join("%s=%r" % kv for kv in self.items())


collections.abc.Mapping.register(Statistics)
_core.register_value_classes(statistics=Statistics)


# ---------------------------------------------------------------- the solver


def _ms(value, what):
    if value is None:
        return None
    if isinstance(value, bool):
        raise TypeError("%s is an int of milliseconds, not a bool" % what)
    if isinstance(value, datetime.timedelta):
        return int(round(value.total_seconds() * 1000))
    if isinstance(value, (int, float)):
        if value < 0:
            raise ArgumentError("%s cannot be negative (%r)" % (what, value), code=ErrorCode.INVALID_ARGUMENT)
        return int(round(value))
    raise TypeError("%s is an int of milliseconds or a timedelta, got %s" % (what, type(value).__name__))


def _count(value, what):
    if value is None:
        return None
    if isinstance(value, bool) or not isinstance(value, int):
        raise TypeError("%s is an int, got %s" % (what, type(value).__name__))
    if value < 0:
        raise ArgumentError("%s cannot be negative (%d)" % (what, value), code=ErrorCode.INVALID_ARGUMENT)
    return value


class Solver(_core.SolverHandle):
    """One solver over a term manager; any number may be live over one manager, each with
    its own assertion stack, options and models.
    `with s:` is push/pop (z3py). Lifetime is garbage collection; close() releases early.
    A check releases the GIL; interrupt() takes no lock and works from any thread; Ctrl-C
    reaches a check running on the main thread (KeyboardInterrupt, solver still usable)."""

    def __init__(self, tm=None, options=None, *, ctx=None, **option_kwargs):
        tm = _tm(tm, ctx)
        handle = None
        if options is not None:
            if isinstance(options, Options):
                handle = options.copy()._handle
            elif isinstance(options, _core.OptionsHandle):
                handle = options.copy()
            elif isinstance(options, dict):
                handle = _core.OptionsHandle()
                Options._wrap(handle).set(options)
            else:
                raise TypeError("options must be an Options object, got %s" % type(options).__name__)
        if option_kwargs:
            if handle is None:
                handle = _core.OptionsHandle()
            Options._wrap(handle).set(**option_kwargs)
        super().__init__(tm, handle)
        self._options_view = None
        self._last = None

    # ------------------------------------------------------------ options
    @property
    def options(self):
        """The live view: timing (the entry's Settable window) is enforced."""
        if self._options_view is None:
            self._options_view = Options._live(self)
        return self._options_view

    def set(self, *positional_pairs, **kwargs):
        self.options.set(*positional_pairs, **kwargs)

    def set_args(self, *argv):
        self.options.set_args(*argv)

    def help(self):
        return _core.option_help(-1)

    def manager(self):
        return self._manager()

    # ------------------------------------------------------------ assertions
    def add(self, *fs):
        tm = self._manager()
        b = tm.bool_sort()
        for f in _flatten_bools(fs):
            self.assert_(_coerce_arg(b, f))

    append = add
    insert = add

    def __iadd__(self, f):
        self.add(f)
        return self

    def assertions(self):
        return _core.SolverHandle.assertions(self)

    def push(self, n=1):
        _core.SolverHandle.push(self, n)

    def pop(self, n=1):
        _core.SolverHandle.pop(self, n)

    def num_scopes(self):
        return self.level()

    def __enter__(self):
        self.push()
        return self

    def __exit__(self, *exc):
        self.pop()
        return False

    def reset_assertions(self):
        _core.SolverHandle.reset_assertions(self)

    def reset(self):
        _core.SolverHandle.reset(self)
        self._last = None

    # ------------------------------------------------------------ checks
    def check(self, *assumptions, timeout=None, conflicts=None):
        """check-sat(-assuming); `timeout` in milliseconds (z3py's unit), overriding max-time for
        this call only; one iterable argument is accepted as in add()."""
        tm = self._manager()
        b = tm.bool_sort()
        terms = [_coerce_arg(b, a) for a in _flatten_bools(assumptions)]
        kind, reason, message = self.check_sat(terms, _ms(timeout, "timeout"), _count(conflicts, "conflicts"))
        self._last = CheckSatResult(kind, reason, message)
        return self._last

    def entails(self, f, timeout=None, conflicts=None):
        tm = self._manager()
        f = _coerce_arg(tm.bool_sort(), f)
        kind, reason, message = _core.SolverHandle.entails(self, f, _ms(timeout, "timeout"),
                                                            _count(conflicts, "conflicts"))
        result = EntailmentResult(kind, reason, message)
        self._last = CheckSatResult(_core.RESULT_UNKNOWN if result.is_unknown() else
                                    (_core.RESULT_SAT if result.is_invalid() else _core.RESULT_UNSAT),
                                    reason, message)
        return result

    def unsat_assumptions(self):
        return _core.SolverHandle.unsat_assumptions(self)

    unsat_core = unsat_assumptions

    def model(self):
        return _core.SolverHandle.model(self)

    def candidate_model(self):
        return _core.SolverHandle.candidate_model(self)

    def value(self, t):
        return self.model()[t]

    def reason_unknown(self):
        if self._last is None:
            return UnknownReason.NONE
        return self._last.reason

    def last_result(self):
        return self._last

    def statistics(self):
        return _core.SolverHandle.statistics(self)

    def set_terminator(self, fn):
        _core.SolverHandle.set_terminator(self, fn)

    # ------------------------------------------------------------ scripts and printing
    def from_string(self, text, format="smtlib2", mode="declare-and-assert"):
        """Parse text into this solver (declarations, assertions, push/pop, options). A ParseError
        leaves the solver unchanged. The mode is "declare-and-assert" (nothing is decided),
        "execute" (the input runs as the stp command line runs it: an SMT-LIB 2 script's
        commands answer, a CVC or SMT-LIB 1 query is decided and answered, to the output sink)
        or "parse-only" (read as the command line's --parse-only reads it)."""
        code = _format_code(format)
        m = _parse_mode(mode)
        if m == _core.PARSE_DECLARE_AND_ASSERT and code not in (_core.FORMAT_SMTLIB2, _core.FORMAT_AUTO):
            self.parse(text, code)
        elif code in (_core.FORMAT_SMTLIB2, _core.FORMAT_AUTO):
            self.parse_smt2(text, m)
        else:
            self.parse_source(text, code, m)

    def from_stream(self, stream, format="smtlib2", mode="execute"):
        """Parse a readable stream as its data arrives (a binary stream's read1, else a line at a
        time), as the stp command line reads its input; the modes are from_string's."""
        self.parse_source(stream, _format_code(format), _parse_mode(mode))

    def from_file(self, path, format="auto"):
        self.parse_file(os.fspath(path), _format_code(format))

    def input_to_string(self, format="cvc"):
        """The last CVC or SMT-LIB 1 input's question, as the stp command line's --print-back
        options print it: "cvc", "smtlib2", "gdl" or "dot"."""
        return _core.SolverHandle.input_to_string(self, _format_code(format))

    def to_smt2(self, with_check_sat=False):
        return _core.SolverHandle.to_smt2(self, with_check_sat)

    def sexpr(self):
        return self.to_smt2(False)

    def to_string(self, format="smtlib2"):
        return _core.SolverHandle.to_string(self, _format_code(format))

    def write_cnf(self, path_or_file):
        """Encode the assertions up to CNF without solving and write the DIMACS text."""
        data = _core.SolverHandle.write_cnf(self)
        if isinstance(path_or_file, (str, bytes, os.PathLike)):
            with open(path_or_file, "wb") as f:
                f.write(data)
        elif isinstance(path_or_file, io.TextIOBase):
            path_or_file.write(data.decode("utf-8", "replace"))
        elif hasattr(path_or_file, "write"):
            try:
                path_or_file.write(data)
            except TypeError:
                path_or_file.write(data.decode("utf-8", "replace"))
        else:
            raise TypeError("write_cnf takes a path or a file object")

    def dimacs(self):
        """The DIMACS text as a str."""
        return _core.SolverHandle.write_cnf(self).decode("utf-8", "replace")

    def __repr__(self):
        if self.closed:
            return "Solver(closed)"
        return "[%s]" % ", ".join(str(a) for a in self.assertions())


# ---------------------------------------------------------------- the model


class Model(_core.ModelHandle):
    """A detached snapshot of the last check that answered sat. Survives every later solver
    operation; never mutates. Completion is explicit: m[t] is a mapping lookup and raises
    KeyError (naming the missing symbol) if evaluating t would need a symbol the solver never
    saw; m.eval(t) completes such symbols with their sort's default; m.get(t, default) is the
    mapping idiom. A term of another manager is translated by name first."""

    def manager(self):
        return self._manager()

    def _key(self, t):
        if isinstance(t, bool):
            return self._manager().mk_bool(t)
        if not isinstance(t, ExprRef):
            raise TypeError("a model is indexed by terms, got %s" % type(t).__name__)
        if t._manager() is not self._manager():
            t = t.translate(self._manager())
        return t

    def _missing(self, t):
        names = []
        seen = set()
        stack = [t]
        while stack:
            u = stack.pop()
            if u.id in seen:
                continue
            seen.add(u.id)
            if u.is_const():
                if not self.in_core(u):
                    names.append(u.decl_name() or u.sexpr())
            else:
                stack.extend(u.children())
        return names

    def __getitem__(self, t):
        t = self._key(t)
        if isinstance(t, FuncRef):
            if not self.in_core(t):
                raise KeyError("function %s is not in the model" % (t.decl_name() or t.sexpr()))
            return self.fun_value(t)
        # the mapping rule: stp_model_try_value refuses every term whose value would need
        # completion, and the KeyError names the symbols outside the core, if that is why
        v = self.try_value(t)
        if v is None:
            missing = self._missing(t)
            if missing:
                raise KeyError("symbol%s %s not in the model (m.eval(t) completes)" %
                               ("" if len(missing) == 1 else "s", ", ".join(missing)))
            raise KeyError("%s cannot be evaluated without completion (m.eval(t) completes)" % t.sexpr())
        if isinstance(t, ArrayRef):
            return ArrayNumRef._from_value(self.array_value(t))
        return v

    def get(self, t, default=None):
        try:
            return self[t]
        except KeyError:
            return default

    def eval(self, t, model_completion=True):
        """The value of t. model_completion=True (the default): symbols outside the core take
        their sort's default (never None). model_completion=False: the core's values are
        substituted, the result simplified, and symbols outside the core left in place (z3py)."""
        t = self._key(t)
        if isinstance(t, FuncRef):
            return self.fun_value(t)
        if model_completion:
            if isinstance(t, ArrayRef):
                return ArrayNumRef._from_value(self.array_value(t))
            return self.value(t)
        pairs = []
        seen = set()
        stack = [t]
        while stack:
            u = stack.pop()
            if u.id in seen:
                continue
            seen.add(u.id)
            if u.is_const():
                if not isinstance(u, FuncRef) and self.in_core(u):
                    pairs.append((u, self.value(u)))
            else:
                stack.extend(u.children())
        r = t.substitute(*pairs) if pairs else t
        return self._manager().simplify_term(r)

    evaluate = eval

    def values(self, ts):
        ts = [self._key(t) for t in ts]
        return _core.ModelHandle.values(self, ts)

    def decls(self):
        return self.symbols()

    def in_core(self, symbol):
        return _core.ModelHandle.in_core(self, self._key(symbol))

    def array_bytes(self, array, first_index, count):
        return _core.ModelHandle.array_bytes(self, self._key(array), first_index, count)

    def to_smt2(self):
        return _core.ModelHandle.to_smt2(self)

    def sexpr(self):
        return self.to_smt2()

    def __str__(self):
        parts = []
        for d in self.decls():
            name = d.decl_name() or d.sexpr()
            if isinstance(d, FuncRef):
                parts.append("%s = %r" % (name, self.fun_value(d)))
            else:
                parts.append("%s = %s" % (name, self.eval(d)))
        return "[" + ", ".join(parts) + "]"

    def __repr__(self):
        return self.to_smt2()

    def __len__(self):
        return self.num_symbols()

    def __iter__(self):
        return iter(self.decls())

    def __contains__(self, t):
        try:
            self[t]
            return True
        except (KeyError, TypeError):
            return False

    def translate(self, tm):
        if tm is self._manager():
            return self
        return Model.from_smt2(self.to_smt2(), tm)

    def __reduce__(self):
        return (Model.from_smt2, (self.to_smt2(),))

    @staticmethod
    def from_smt2(text, tm=None):
        """Rebuild a model from the text of to_smt2() on tm (a private TermManager with
        tm=None), through a scratch solver of its own; the solvers already live over tm are
        untouched. Lookups with terms of other managers translate them by name."""
        from . import _smt2
        if tm is None:
            tm = TermManager()
        elif not isinstance(tm, TermManager):
            raise TypeError("tm must be a TermManager")
        return _smt2.model_from_smt2(text, tm, _model_of_constraints)


_core.register_value_classes(model=Model)


def _model_of_constraints(tm, constraints):
    """A Model in which every constraint holds (the pinned values of a rebuilt model), built
    on tm by a scratch solver of its own; the solvers already live over tm are untouched."""
    s = Solver(tm)
    try:
        s.add(*constraints)
        r = s.check()
        if r != sat:
            raise StateError("the model text is not consistent with this manager (%s)" % r,
                             code=ErrorCode.STATE, function="Model.from_smt2")
        return s.model()
    finally:
        s.close()


# ---------------------------------------------------------------- conveniences


def SolverFor(logic, tm=None, ctx=None, **options):
    """A solver with the `logic` option set (QF_BV, QF_ABV, QF_AUFBV, QF_BVFP, QF_LRA, ...)."""
    return Solver(_tm(tm, ctx), logic=logic, **options)


def SimpleSolver(tm=None, ctx=None, **options):
    return Solver(_tm(tm, ctx), **options)


def _manager_of(fs, tm):
    if tm is not None:
        return tm
    for f in fs:
        if isinstance(f, ExprRef):
            return f._manager()
    return main_tm()


@contextlib.contextmanager
def _scratch_solver(tm, fs, **options):
    """A fresh solver on tm to run one query in; the solvers already live over tm are
    untouched."""
    s = Solver(tm, **options)
    try:
        yield s, fs
    finally:
        s.close()


def solve(*fs, tm=None, ctx=None, show=True, **options):
    """Check the conjunction of fs; print the model, "no solution" or the reason (z3py) and
    return the result."""
    tm = _manager_of(fs, _tm(tm, ctx) if (tm is not None or ctx is not None) else None)
    with _scratch_solver(tm, fs, **options) as (s, fs2):
        s.add(*fs2)
        r = s.check()
        if show:
            if r == sat:
                print(s.model())
            elif r == unsat:
                print("no solution")
            else:
                print("failed to solve: %s" % r.reason.value)
        return r


def prove(f, tm=None, ctx=None, show=True, **options):
    """Prove f (check that its negation is unsat); print "proved" or a counterexample."""
    tm = _manager_of([f], _tm(tm, ctx) if (tm is not None or ctx is not None) else None)
    with _scratch_solver(tm, [f], **options) as (s, fs2):
        r = s.entails(fs2[0])
        if show:
            if r == valid:
                print("proved")
            elif r == invalid:
                print("counterexample")
                print(s.model())
            else:
                print("failed to prove: %s" % r.reason.value)
        return r


def parse_smt2_string(text, tm=None, ctx=None):
    """The formulas asserted by an SMT-LIB 2 script (its declarations enter tm's name table)."""
    tm = _tm(tm, ctx)
    s = Solver(tm)
    try:
        s.from_string(text)
        return s.assertions()
    finally:
        s.close()


def parse_smt2_file(path, tm=None, ctx=None):
    with open(path, "r", encoding="utf-8") as f:
        return parse_smt2_string(f.read(), tm, ctx)


# ---------------------------------------------------------------- the current solver (2.x style)

_current = threading.local()


def current_solver():
    """The thread-local current solver set by solver_scope(s), or None."""
    return getattr(_current, "solver", None)


@contextlib.contextmanager
def solver_scope(s):
    """with solver_scope(s): add()/check()/model() and @stp functions use s."""
    if not isinstance(s, Solver):
        raise TypeError("solver_scope takes a Solver")
    previous = getattr(_current, "solver", None)
    _current.solver = s
    try:
        yield s
    finally:
        _current.solver = previous


def _need_current(what):
    s = current_solver()
    if s is None:
        raise StateError("%s needs a current solver: use `with solver_scope(s):`" % what,
                         code=ErrorCode.STATE, function=what)
    return s


def add(*fs):
    _need_current("add").add(*fs)


def check(*assumptions, **kw):
    return _need_current("check").check(*assumptions, **kw)


def model():
    return _need_current("model").model()


class _ASTtoSTP(ast.NodeVisitor):
    """The 2.x decorator's evaluator: a function body read as constraints over bit-vectors.
    Arguments not supplied at the call become 32-bit symbols (a default value gives the
    width), `assert` statements are added to the current solver and `return` yields a term."""

    def __init__(self, solver, count, args, kwargs):
        super().__init__()
        self.s = solver
        self.count = count
        self.inside = False
        self.func_name = None
        self.names = {}
        self.exprs = []
        self.returned = None
        self.args = args
        self.kwargs = kwargs

    def visit_Module(self, node):
        for stmt in node.body:
            self.visit(stmt)

    def visit_FunctionDef(self, node):
        if node.args.vararg is not None or node.args.kwarg is not None:
            raise TypeError("@stp: variable and keyword arguments are not allowed")
        if self.inside:
            raise TypeError("@stp: nested functions are not allowed")
        self.inside = True
        self.func_name = node.name
        params = node.args.args
        defaults = node.args.defaults
        first_default = len(params) - len(defaults)
        tm = self.s.manager()
        for idx, param in enumerate(params):
            arg = param.arg
            if idx < len(self.args):
                self.names[arg] = self.args[idx]
                continue
            if arg in self.kwargs:
                self.names[arg] = self.kwargs[arg]
                continue
            width = 32
            if idx >= first_default:
                d = defaults[idx - first_default]
                if isinstance(d, ast.Constant) and isinstance(d.value, int):
                    width = d.value
            self.names[arg] = BitVec("%s_%d_%s" % (self.func_name, self.count, arg), width, tm=tm)
        for stmt in node.body:
            self.visit(stmt)

    def visit_Constant(self, node):
        if isinstance(node.value, (bool, int, float)):
            return node.value
        raise TypeError("@stp: literal %r is not supported" % (node.value,))

    def visit_BoolOp(self, node):
        values = [self.visit(v) for v in node.values]
        if isinstance(node.op, ast.And):
            return And(*values)
        if isinstance(node.op, ast.Or):
            from ._terms import Or
            return Or(*values)
        raise TypeError("@stp: %s is not supported" % type(node.op).__name__)

    def visit_UnaryOp(self, node):
        v = self.visit(node.operand)
        if isinstance(node.op, ast.Not):
            return Not(v)
        if isinstance(node.op, ast.USub):
            return -v
        if isinstance(node.op, ast.Invert):
            return ~v
        if isinstance(node.op, ast.UAdd):
            return v
        raise TypeError("@stp: %s is not supported" % type(node.op).__name__)

    _BINOPS = {
        ast.Add: lambda x, y: x + y,
        ast.Sub: lambda x, y: x - y,
        ast.Mult: lambda x, y: x * y,
        ast.Div: lambda x, y: x / y,
        ast.FloorDiv: lambda x, y: x // y,
        ast.Mod: lambda x, y: x % y,
        ast.LShift: lambda x, y: x << y,
        ast.RShift: lambda x, y: x >> y,
        ast.BitOr: lambda x, y: x | y,
        ast.BitXor: lambda x, y: x ^ y,
        ast.BitAnd: lambda x, y: x & y,
    }

    def visit_BinOp(self, node):
        op = self._BINOPS.get(type(node.op))
        if op is None:
            raise TypeError("@stp: %s is not supported" % type(node.op).__name__)
        return op(self.visit(node.left), self.visit(node.right))

    _CMPS = {
        ast.Eq: lambda x, y: x == y,
        ast.NotEq: lambda x, y: x != y,
        ast.Lt: lambda x, y: x < y,
        ast.LtE: lambda x, y: x <= y,
        ast.Gt: lambda x, y: x > y,
        ast.GtE: lambda x, y: x >= y,
        ast.Is: lambda x, y: x == y,
        ast.IsNot: lambda x, y: x != y,
    }

    def visit_Compare(self, node):
        left = self.visit(node.left)
        parts = []
        for op, comparator in zip(node.ops, node.comparators):
            right = self.visit(comparator)
            cmp = self._CMPS.get(type(op))
            if cmp is None:
                raise TypeError("@stp: %s is not supported" % type(op).__name__)
            parts.append(cmp(left, right))
            left = right
        return parts[0] if len(parts) == 1 else And(*parts)

    def visit_Name(self, node):
        if isinstance(node.ctx, ast.Load):
            try:
                return self.names[node.id]
            except KeyError:
                raise NameError("@stp: %s is not an argument or an assigned name" % node.id) from None
        raise TypeError("@stp: unsupported use of the name %s" % node.id)

    def visit_Assign(self, node):
        value = self.visit(node.value)
        for target in node.targets:
            if not isinstance(target, ast.Name):
                raise TypeError("@stp: only simple assignments are supported")
            self.names[target.id] = value

    def visit_Assert(self, node):
        self.exprs.append(self.visit(node.test))

    def visit_Return(self, node):
        self.returned = self.visit(node.value) if node.value is not None else None

    def visit_Expr(self, node):
        self.visit(node.value)

    def visit_Pass(self, node):
        return None

    def generic_visit(self, node):
        raise TypeError("@stp: %s is not yet supported" % type(node).__name__)


def stp(fn):
    """The 2.x decorator: each call of the decorated function evaluates its body symbolically
    over the current solver (solver_scope): missing arguments become 32-bit symbols, `assert`
    adds constraints, `return` gives the term. The function must live in a source file."""
    try:
        src = inspect.getsource(fn)
    except (OSError, TypeError):
        raise TypeError("@stp works on functions stored in a source file, not on ones typed at the prompt") from None
    tree = ast.parse(inspect.cleandoc(src) if src.startswith((" ", "\t")) else src)
    # drop the decorator list so that the visitor never sees it
    for node in tree.body:
        if isinstance(node, ast.FunctionDef):
            node.decorator_list = []
    count = [0]

    def wrapper(*args, **kwargs):
        s = _need_current("@stp " + fn.__name__)
        count[0] += 1
        visitor = _ASTtoSTP(s, count[0] - 1, args, kwargs)
        visitor.visit(tree)
        if visitor.exprs:
            s.add(*visitor.exprs)
        return visitor.returned

    wrapper.__name__ = fn.__name__
    wrapper.__doc__ = fn.__doc__
    wrapper.__wrapped__ = fn
    return wrapper
