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

"""The exception hierarchy and the fields every error carries."""

import pytest

from stp import *
import stp


def test_hierarchy():
    assert issubclass(ArgumentError, Error) and issubclass(ArgumentError, ValueError)
    assert issubclass(SortMismatch, ArgumentError) and issubclass(SortMismatch, TypeError)
    assert issubclass(DoesNotFit, Error) and issubclass(DoesNotFit, OverflowError)
    assert issubclass(NotAValue, Error) and issubclass(NotAValue, TypeError)
    assert issubclass(NoModel, Error) and not issubclass(NoModel, ValueError)
    assert issubclass(Unsupported, Error) and issubclass(Unsupported, NotImplementedError)
    assert issubclass(OptionError, Error) and issubclass(OptionError, ValueError)
    assert issubclass(UnknownOption, OptionError) and issubclass(UnknownOption, KeyError)
    assert issubclass(ParseError, Error) and issubclass(ParseError, ValueError) and not issubclass(ParseError, SyntaxError)
    assert issubclass(stp.IOError, Error) and issubclass(stp.IOError, OSError)
    assert issubclass(StateError, Error) and issubclass(StateError, RuntimeError)
    assert issubclass(ResourceError, Error) and issubclass(ResourceError, MemoryError)
    assert issubclass(InternalError, Error) and issubclass(Error, Exception)
    for cls in (Error, ArgumentError, SortMismatch, DoesNotFit, NotAValue, NoModel, Unsupported, OptionError,
                UnknownOption, ParseError, stp.IOError, StateError, ResourceError, InternalError):
        e = cls("a message")
        assert str(e) == "a message" and e.message == "a message" and e.recoverable is True
        assert e.code is None and e.function == "" and e.argument_index is None and e.option is None
    assert str(UnknownOption("unknown option 'x'")) == "unknown option 'x'"  # not KeyError's repr-quoting


def test_sort_mismatch_fields():
    u, v = BitVec("u", 8), BitVec("v", 16)
    with pytest.raises(SortMismatch) as e:
        u + v
    err = e.value
    assert err.code == ErrorCode.SORT_MISMATCH and err.code.name == "SORT_MISMATCH"
    assert err.recoverable is True and err.argument_index == 1
    assert err.function.startswith("stp_")
    assert "(_ BitVec 16)" in str(err) and "(_ BitVec 8)" in str(err)
    assert len(err.terms) >= 1 and all(isinstance(t, ExprRef) for t in err.terms)
    assert u in err.terms or v in err.terms
    # also catchable as the built-in
    with pytest.raises(TypeError):
        u + v
    with pytest.raises(ValueError):
        u + v


def test_a_foreign_term_is_its_own_managers():
    a, b = TermManager(), TermManager()
    y = BitVec("y", 8, tm=b)
    with pytest.raises(SortMismatch) as e:
        a.simplify_term(y)
    err = e.value
    assert err.code == ErrorCode.FOREIGN_MANAGER
    # the one wrapper of the other manager's node, not a new one of a's
    assert len(err.terms) == 1 and err.terms[0] is y
    assert err.terms[0]._manager() is b

def test_argument_errors():
    with pytest.raises(ArgumentError) as e:
        BitVecVal(300, 8)
    assert e.value.code == ErrorCode.VALUE_OUT_OF_RANGE
    with pytest.raises(ArgumentError) as e:
        Extract(8, 0, BitVec("x", 8))
    assert e.value.code in (ErrorCode.INVALID_ARGUMENT, ErrorCode.INDEX_OUT_OF_RANGE)
    with pytest.raises(ArgumentError) as e:
        Function("f", BitVecSort(8), BitVecSort(8))(1, 2)
    assert e.value.code == ErrorCode.ARITY
    with pytest.raises(ArgumentError) as e:
        Q(1, 0)
    assert e.value.code == ErrorCode.INVALID_ARGUMENT
    s = Solver()
    with pytest.raises(ArgumentError) as e:
        s.pop()
    assert e.value.code == ErrorCode.INVALID_ARGUMENT
    assert s.check() == sat  # the solver is still usable: Python needs no failed state
    s.close()


def test_reader_errors():
    x = BitVec("x", 8)
    with pytest.raises(NotAValue):
        BitVecNumRef.as_long(x)  # not a value
    with pytest.raises(DoesNotFit) as e:
        float(FPVal(1.0, Float128()))
    assert e.value.code == ErrorCode.DOES_NOT_FIT and isinstance(e.value, OverflowError)
    with pytest.raises(SortMismatch):
        s = Solver()
        s.add(x)  # not a Bool
    s.close()


def test_no_model_and_state_errors():
    s = Solver()
    x = BitVec("x", 8)
    s.add(x == 1, x == 2)
    assert s.check() == unsat
    with pytest.raises(NoModel) as e:
        s.model()
    assert e.value.code == ErrorCode.NO_MODEL
    with pytest.raises(NoModel):
        s.value(x)
    assert s.unsat_assumptions() == []  # unsat without assumptions: the empty subset
    s.reset_assertions()
    s.add(x == 1)
    assert s.check() == sat
    with pytest.raises(StateError):
        s.unsat_assumptions()
    s.close()
    with pytest.raises(StateError) as e:
        s.check()
    assert e.value.code is None or e.value.code == ErrorCode.STATE
    s.close()  # idempotent


def test_unsupported_and_parse_errors():
    with pytest.raises(Unsupported) as e:
        Real("p") * Real("q")  # non-linear
    assert e.value.code == ErrorCode.UNSUPPORTED and isinstance(e.value, NotImplementedError)
    s = Solver()
    with pytest.raises(ParseError) as e:
        s.from_string("(declare-fun x () (_ BitVec 8)) (assert (= x")
    err = e.value
    assert err.code == ErrorCode.PARSE and err.lineno == 1 and err.line == 1 and err.offset == err.column
    assert isinstance(err, ValueError)
    assert s.assertions() == []  # the failed parse left the solver unchanged
    with pytest.raises(ParseError):
        s.parse_term("(bvadd x x x")
    with pytest.raises(stp.IOError) as e:
        s.from_file("/nonexistent/path/to/file.smt2")
    assert e.value.code == ErrorCode.IO and isinstance(e.value, OSError)
    s.close()


def test_a_sort_error_in_a_script_is_a_parse_error():
    # operands of two widths are refused as the term is built: the script's
    # own failure, which used to poison the default manager for the process
    x = BitVec("x", 8)
    s = Solver()
    s.add(x == 3)
    with pytest.raises(ParseError):
        s.from_string("(declare-fun z () (_ BitVec 8))(assert (bvult z #b1))")
    assert len(s.assertions()) == 1 and s.check() == sat
    assert (BitVecVal(1, 8) + x).sort() == BitVecSort(8)
    s.close()


def test_option_errors():
    with pytest.raises(UnknownOption) as e:
        Options(no_such_option=1)
    assert e.value.code == ErrorCode.OPTION_UNKNOWN and e.value.option == "no_such_option"
    assert isinstance(e.value, KeyError) and "no_such_option" in str(e.value)
    with pytest.raises(OptionError) as e:
        Options(max_time=True)
    assert e.value.code == ErrorCode.OPTION_VALUE and e.value.option == "max-time"
    with pytest.raises(OptionError) as e:
        Options(sat_backend="no-such-backend")
    assert e.value.code in (ErrorCode.OPTION_VALUE, ErrorCode.OPTION_UNAVAILABLE)


def test_error_code_enum():
    assert ErrorCode.RESOURCE == 100 and ErrorCode.INTERNAL == 101 and ErrorCode.INVALID_ARGUMENT == 1
    assert Kind.BV_ADD.smtlib == "bvadd" and Kind.EQUAL.smtlib == "="
    assert UnknownReason.TIMEOUT == "timeout" and UnknownReason("conflict-limit") is UnknownReason.CONFLICT_LIMIT
    assert hash(UnknownReason.TIMEOUT) == hash("timeout") and str(UnknownReason.INTERRUPTED) == "interrupted"
    assert Tier.STABLE == 0 and RoundingMode.RTZ == 4 and SortKind.FUN == 6
