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

"""Solver: assertions, scopes, checks with assumptions and budgets, results, entailment,
statistics, scripts and printing, the conveniences (SolverFor, solve, prove, @stp)."""

import io
import time

import pytest

from stp import *
import stp
from conftest import hard_solver, interruptible_backend


def test_check_and_results():
    x, y = BitVecs("x y", 8)
    s = Solver()
    s.add(x + y == 10, ULT(x, 3))
    r = s.check()
    assert r == sat and r.is_sat() and not r.is_unsat() and not r.is_unknown()
    assert r.reason == UnknownReason.NONE and r.reason_message == "" and repr(r) == "sat" and str(r) == "sat"
    assert r != unsat and r != unknown and hash(r) == hash(sat)
    with pytest.raises(TypeError):
        bool(r)
    with pytest.raises(TypeError):
        if sat:
            pass
    assert (sat == unsat) is False and (sat == 1) is False and sat != "sat"
    m = s.model()
    assert m[x].as_long() < 3 and (m[x].as_long() + m[y].as_long()) % 256 == 10
    s.add(x == 5)
    assert s.check() == unsat and s.reason_unknown() == UnknownReason.NONE
    assert repr(s.check()) == "unsat"
    assert s.last_result() == unsat
    s.close()


def test_add_forms_and_assertions():
    p, q, r = Bools("p q r")
    s = Solver()
    s.add(p)
    s.add(q, r)
    s.add([Not(p) | q])
    s += Implies(q, r)
    s.append(True)
    s.insert(Or(p, q))
    assert len(s.assertions()) == 7
    assert all(isinstance(a, BoolRef) for a in s.assertions())
    assert s.assertions()[0] is p
    with pytest.raises(SortMismatch):
        s.add(BitVec("x", 8))
    with pytest.raises(TypeError):
        s.add(3)
    assert len(s.assertions()) == 7  # the refused adds left nothing behind
    assert repr(s).startswith("[") and "p" in repr(s)
    assert s.check() == sat
    s.reset_assertions()
    assert s.assertions() == [] and s.check() == sat
    s.set(max_time=100)
    s.reset()
    assert s.assertions() == [] and s.options["max_time"] is None
    s.close()


def test_push_pop_scopes():
    x = BitVec("x", 8)
    s = Solver()
    s.add(ULT(x, 10))
    assert s.num_scopes() == 0
    s.push()
    assert s.num_scopes() == 1
    s.add(x == 20)
    assert s.check() == unsat
    s.pop()
    assert s.num_scopes() == 0 and s.check() == sat
    with s:
        s.add(x == 30)
        assert s.num_scopes() == 1 and s.check() == unsat
    assert s.num_scopes() == 0 and s.check() == sat
    s.push(2)
    assert s.num_scopes() == 2
    s.pop(2)
    with pytest.raises(ArgumentError):
        s.pop()
    assert s.check() == sat  # still usable
    with pytest.raises(ArgumentError):
        s.pop(3)
    s.close()


def test_assumptions_and_unsat_core():
    p, q = Bools("p q")
    x = BitVec("x", 32)
    s = Solver()
    s.add(Implies(p, x == 0))
    r = s.check(p, x != 0)
    assert r == unsat
    core = s.unsat_assumptions()
    assert len(core) == 2 and any(t is p for t in core)
    assert s.unsat_core() == core
    assert s.check([p]) == sat and s.model()[x].as_long() == 0
    with pytest.raises(StateError):
        s.unsat_assumptions()  # after sat
    assert s.check(q) == sat and s.check() == sat
    assert s.check(p, q, x == 0) == sat
    s.add(p)
    assert s.check(x != 0) == unsat and len(s.unsat_assumptions()) == 1
    assert s.check() == sat
    with pytest.raises(TypeError):
        s.check(3)
    s.close()


def test_budgets(hard):
    r = hard.check(timeout=0)
    assert r == unknown and r.is_unknown() and r.reason == UnknownReason.TIMEOUT and r.reason == "timeout"
    assert "budget" in r.reason_message or "time" in r.reason_message
    assert repr(r) == "unknown (timeout)" and hard.reason_unknown() == UnknownReason.TIMEOUT
    t0 = time.monotonic()
    r = hard.check(timeout=300)
    elapsed = time.monotonic() - t0
    assert r == unknown and r.reason == UnknownReason.TIMEOUT and elapsed < 10
    r = hard.check(conflicts=5)
    assert r == unknown and r.reason == UnknownReason.CONFLICT_LIMIT and r.reason == "conflict-limit"
    import datetime
    assert hard.check(timeout=datetime.timedelta(milliseconds=50)).reason == UnknownReason.TIMEOUT
    with pytest.raises(ArgumentError):
        hard.check(timeout=-1)
    with pytest.raises(TypeError):
        hard.check(timeout="1s")
    # the persistent option
    hard.set(max_time=100)
    assert hard.check().reason == UnknownReason.TIMEOUT
    assert hard.candidate_model() is None or isinstance(hard.candidate_model(), Model)
    with pytest.raises(NoModel):
        hard.model()


def test_entails():
    x, y = BitVecs("x y", 8)
    s = Solver()
    s.add(ULT(x, 10), ULT(y, x))
    r = s.entails(ULT(y, 10))
    assert r == valid and r.is_valid() and not r.is_invalid() and repr(r) == "valid" and hash(r) == hash(valid)
    r = s.entails(ULT(y, 3))
    assert r == invalid and r.is_invalid()
    m = s.model()  # the countermodel
    assert m[y].as_long() >= 3 and m[y].as_long() < m[x].as_long() < 10
    with pytest.raises(TypeError):
        bool(r)
    assert unknown != valid and (valid == sat) is False
    assert s.entails(True) == valid
    with pytest.raises(SortMismatch):
        s.entails(x)
    s.close()


def test_solver_options_and_manager():
    tm = main_tm()
    s = Solver(max_time=500, random_seed=7)
    assert s.manager() is tm and s.options["max_time"] == 500 and s.options["random_seed"] == 7
    assert s.options.live and "sat-backend" in s.help()
    s2 = Solver(tm=TermManager(), produce_models=False)
    assert s2.options["produce_models"] is False and s2.manager() is not tm
    s2.close()
    s4 = Solver()  # any number of solvers over one manager
    assert s4.manager() is tm and s4.check() == sat
    s4.close()
    s.close()
    s3 = Solver(ctx=tm)  # z3py's ctx= alias
    assert s3.manager() is tm
    s3.close()
    with pytest.raises(TypeError):
        Solver(options=3)


def test_statistics():
    x = BitVec("x", 32)
    s = Solver()
    s.add(x * x == 1)
    assert s.check() == sat
    st = s.statistics()
    assert isinstance(st, Statistics) and isinstance(st, __import__("collections.abc").abc.Mapping)
    assert len(st) > 0 and "checks.total" in st and "sat.backend" in st
    assert st["checks.total"] >= 1 and isinstance(st["checks.total"], int)
    assert isinstance(st["sat.backend"], str) and st["sat.backend"] in sat_backends()
    assert isinstance(st["time.total_ms"], float)
    assert st.tier("checks.total") == Tier.STABLE
    assert st.get("no.such", 42) == 42 and "no.such" not in st
    with pytest.raises(KeyError):
        st["no.such"]
    with pytest.raises(ArgumentError):
        st.tier("no.such")
    assert set(st.keys()) == set(iter(st)) and len(st.items()) == len(st)
    assert dict(st)["checks.total"] == st["checks.total"]
    assert st["checks.total"] in repr(st) if False else "checks.total" in repr(st)
    s.close()


def test_scripts_and_printing(tmp_path):
    s = Solver()
    s.from_string("(declare-fun a () (_ BitVec 8)) (declare-fun b () (_ BitVec 8)) (assert (= a #x07)) (assert (bvult b a))")
    a, b = s.symbol("a"), s.symbol("b")
    assert a is BitVec("a", 8) and b is main_tm().symbol("b") and s.symbol("zz") is None
    assert len(s.assertions()) == 2
    assert s.check() == sat and s.model()[a].as_long() == 7 and s.model()[b].as_long() < 7
    text = s.to_smt2()
    assert "(declare-fun a () (_ BitVec 8))" in text and "(assert" in text and "(check-sat)" not in text
    assert "(check-sat)" in s.to_smt2(with_check_sat=True) and s.sexpr() == text
    assert s.to_string("smtlib2") == text
    assert "digraph" in s.to_string("dot") or "->" in s.to_string("dot")
    t = s.parse_term("(bvadd a #x01)")
    assert t.kind() == Kind.BV_ADD and t.arg(0) is a or t.arg(1) is a
    with pytest.raises(ParseError):
        s.from_string("(assert (= a")
    assert len(s.assertions()) == 2
    # round trip through a second solver on a fresh manager
    tm2 = TermManager()
    s2 = Solver(tm2)
    s2.from_string(s.to_smt2())
    assert len(s2.assertions()) == 2 and s2.check() == sat and s2.model()[BitVec("a", 8, tm=tm2)].as_long() == 7
    s2.close()
    # from_file, and SMT-LIB 2 as the only input language
    path = tmp_path / "q.smt2"
    path.write_text(s.to_smt2(with_check_sat=True))
    s3 = Solver(TermManager())
    s3.from_file(str(path))
    assert s3.check() == sat
    s3.close()
    s4 = Solver(TermManager())
    with pytest.raises(ArgumentError):
        s4.from_string("(assert true)", format="dot")
    with pytest.raises(ArgumentError):
        s4.from_string("(assert true)", format="pdf")
    s4.close()
    # execute mode answers to the output sink; a diagnostic sink takes the rest
    s5 = Solver(TermManager())
    out, err = [], []
    s5.set_output_sink(out.append)
    s5.set_diagnostic_sink(err.append)
    s5.from_string("(declare-fun z () Bool) (assert z) (check-sat) (get-model)", mode="execute")
    assert "".join(out).startswith("sat\n") and "define-fun" in "".join(out)
    assert s5.check() == sat
    s5.set_output_sink(None)
    s5.set_diagnostic_sink(None)
    with pytest.raises(ArgumentError):
        s5.from_string("(assert true)", mode="run")
    s5.close()
    s.close()


def test_dimacs_leaves_the_last_check_as_it_was():
    # the export runs a check of its own; the model not yet read, and an
    # unsat check's failed assumptions, are still the caller's afterwards
    s = Solver()
    x = BitVec("dx", 8)
    s.add(x == 7)
    assert s.check() == sat
    s.dimacs()
    assert s.model()[x].as_long() == 7
    b = Bool("db")
    assert s.check(b, Not(b)) == unsat
    assert len(s.unsat_core()) == 2
    s.dimacs()
    assert len(s.unsat_core()) == 2
    s.close()


def test_declared_sorts_carry_across_parses():
    s = Solver()
    s.from_string("(declare-sort PS 0) (declare-fun pa () PS)")
    s.from_string("(declare-fun pb () PS) (assert (distinct pa pb))")  # once "unknown sort"
    assert s.check() == sat
    s2 = Solver()
    s2.from_string("(declare-sort PU 0)")
    assert "PU" in [d.name() for d in s2.manager().declared_sorts()]
    s.close()
    s2.close()


@pytest.mark.parametrize("simplify", [False, True])
def test_reset_cannot_replace_persistent_sorts(simplify):
    tm = TermManager(simplify=simplify)
    u = tm.declare_sort("U")
    x, z = tm.declare("x", u), tm.declare("z", u)
    s = Solver(tm)
    s.add(x != z)
    with pytest.raises(ParseError, match="term manager"):
        s.from_string("(reset) (declare-sort U 0) (declare-fun y () U)")
    assert tm.declare_sort("U") == u
    assert tm.symbol("y") is None
    assert s.check() == sat
    assert s.model().eval(x != z)
    s.from_string("(declare-fun y () U) (assert (distinct x y))")
    assert tm.symbol("y").sort() == u
    assert s.check() == sat


@pytest.mark.parametrize("simplify", [False, True])
def test_reset_cannot_retype_persistent_symbols(simplify):
    tm = TermManager(simplify=simplify)
    s = Solver(tm)
    s.from_string("(declare-fun x () (_ BitVec 4)) (assert (= x #x3))")
    x = tm.symbol("x")
    with pytest.raises(ParseError, match="term manager"):
        s.from_string("(reset) (declare-fun x () Bool) (assert x)")
    assert tm.symbol("x") is x
    assert s.check() == sat
    assert s.model()[x].as_long() == 3
    back = Solver(TermManager())
    back.from_string(s.to_smt2())
    assert back.check() == sat
    assert back.model()[back.manager().symbol("x")].as_long() == 3


def test_printed_logic_admits_unused_declarations():
    # a Real no assertion mentions printed under QF_BV, which the execute
    # mode refuses
    s = Solver(TermManager())
    s.from_string("(declare-fun ux () Real)")
    text = s.to_smt2()
    assert text.startswith("(set-logic QF_LRA)")
    t = Solver(TermManager())
    t.from_string(text, mode="execute")
    s.close()
    t.close()


def test_parse_term_runs_no_command():
    # the text goes inside a command of its own; a ')' in it once closed that
    # command and ran what followed against the solver
    s = Solver()
    s.add(BoolVal(False))
    for text in ("true) (reset-assertions) (assert true", "true) (pop 1) (assert false", "true false"):
        with pytest.raises(ParseError):
            s.parse_term(text)
    assert len(s.assertions()) == 1 and s.check() == unsat
    s.close()


def test_inputs_run_as_the_command_line_runs_them():
    script = "(declare-fun x () (_ BitVec 8))\n(assert (= x #x05))\n(assert (not (= x #x05)))\n(check-sat)\n"
    # a script's check decided and answered, in the command line's words
    s = Solver(TermManager())
    out = []
    s.set_output_sink(out.append)
    s.from_string(script, mode="execute")
    assert "".join(out) == "unsat\n"
    # parse-only decides nothing
    s2 = Solver(TermManager())
    out2 = []
    s2.set_output_sink(out2.append)
    s2.from_string(script, mode="parse-only")
    assert "".join(out2) == ""
    assert s2.assertions() and s2.check() == unsat
    s2.close()
    s.close()


def test_a_stream_is_run_as_it_arrives():
    script = "(declare-fun a () (_ BitVec 8))\n(assert (= a #x07))\n(check-sat)\n(echo \"done\")\n"
    for stream in (io.BytesIO(script.encode()), io.StringIO(script)):
        s = Solver(TermManager())
        out = []
        s.set_output_sink(out.append)
        s.from_stream(stream)
        assert "".join(out) == 'sat\n"done"\n'
        s.close()

    # the stream's own exception fails the parse, and the solver is as it was
    class Broken(io.RawIOBase):
        def readable(self):
            return True

        def readline(self, size=-1):
            raise OSError("the pipe broke")

    s = Solver(TermManager())
    with pytest.raises(OSError, match="the pipe broke"):
        s.from_stream(Broken(), mode="declare-and-assert")
    assert len(s.assertions()) == 0 and s.check() == sat
    s.close()


def test_the_cnf_sink_and_the_fatal_error_handler():
    tm = TermManager()
    x, y = BitVecs("x y", 16, tm=tm)
    s = Solver(tm)
    cnfs = []
    s.set_cnf_sink(lambda dimacs, scope: cnfs.append((dimacs, scope)))
    s.add(x * y == 143, UGT(x, 1), UGT(y, 1), ULT(x, 200), ULT(y, 200))
    assert s.check() == sat
    assert cnfs and b"p cnf " in cnfs[0][0] and cnfs[0][1] == "whole"
    s.set_cnf_sink(None)
    # the handler hears of a fatal error before the call fails
    heard = []
    s.set_fatal_error_handler(heard.append)
    with pytest.raises(ParseError):
        s.from_string("(declare-fun z () (_ BitVec 0))\n", mode="execute")
    assert len(heard) == 1 and "bit-vectors must be of positive length" in heard[0]
    s.set_fatal_error_handler(None)
    assert s.check() == sat
    s.close()


def test_write_cnf(tmp_path):
    x, y = BitVecs("x y", 8)
    s = Solver()
    s.add(x + y == 3, ULT(x, y))
    path = tmp_path / "out.cnf"
    assert s.write_cnf(path) == "whole"
    data = path.read_text()
    assert "p cnf" in data
    buf = io.StringIO()
    s.write_cnf(buf)
    assert buf.getvalue() == data
    bbuf = io.BytesIO()
    s.write_cnf(bbuf)
    assert bbuf.getvalue().decode() == data and s.dimacs() == data
    assert s.check() == sat  # writing the CNF leaves the solver usable
    with pytest.raises(TypeError):
        s.write_cnf(3)
    # not a check: a pending interrupt is left for the next one
    s.interrupt()
    assert s.dimacs() == data and s.interrupt_pending()
    assert s.check() == unknown and not s.interrupt_pending()
    s.close()
    # the batch pipeline's CNF, whatever incremental says
    s = Solver(incremental="on")
    s.add(x * y == 6, UGT(x, 1), UGT(y, 1))
    assert "decided before" not in s.dimacs() and "p cnf" in s.dimacs()
    s.close()


def test_terminator():
    s = hard_solver()
    polls = []
    s.set_terminator(lambda: polls.append(1) or len(polls) >= 3)
    r = s.check()
    assert r == unknown and r.reason == UnknownReason.INTERRUPTED and len(polls) >= 3
    s.set_terminator(None)
    assert s.check(timeout=0).reason == UnknownReason.TIMEOUT

    def boom():
        raise ValueError("boom")
    s.set_terminator(boom)
    with pytest.raises(ValueError, match="boom"):
        s.check()
    s.set_terminator(None)
    with pytest.raises(TypeError):
        s.set_terminator(3)
    s.close()


def test_solver_for_and_simple_solver():
    s = SolverFor("QF_BV")
    assert s.options["logic"] == "QF_BV"
    x = BitVec("x", 8)
    s.add(x == 1)
    assert s.check() == sat
    s.close()
    s = SimpleSolver(max_time=1000)
    assert s.options["max_time"] == 1000 and s.check() == sat
    s.close()
    s = SolverFor("QF_ABV", TermManager(), random_seed=3)
    assert s.options["logic"] == "QF_ABV" and s.options["random_seed"] == 3
    s.close()


def test_solve_and_prove(capsys):
    x = BitVec("x", 8)
    r = solve(ULT(x, 5), ULT(3, x))
    out = capsys.readouterr().out
    assert r == sat and "x = 4" in out
    assert solve(ULT(x, 5), ULT(6, x)) == unsat and "no solution" in capsys.readouterr().out
    assert solve(ULT(x, 5), ULT(3, x), show=False) == sat and capsys.readouterr().out == ""
    p = Bool("p")
    assert prove(Or(p, Not(p))) == valid and "proved" in capsys.readouterr().out
    r = prove(ULT(x, 200))
    out = capsys.readouterr().out
    assert r == invalid and "counterexample" in out and "x = " in out
    # a solver already live on the manager is left as it was: solve() runs its own
    s = Solver()
    s.add(x == 1)
    assert solve(x == 2, show=False) == sat and s.check() == sat and s.model()[x].as_long() == 1
    assert prove(x == 1, show=False) == invalid
    s.close()


def test_parse_smt2_string():
    fs = parse_smt2_string("(declare-fun a () (_ BitVec 8)) (assert (= a #x03)) (assert (bvugt a #x01))")
    assert len(fs) == 2 and all(isinstance(f, BoolRef) for f in fs)
    a = BitVec("a", 8)
    assert a is main_tm().symbol("a")
    s = Solver()
    s.add(*fs)
    assert s.check() == sat and s.model()[a].as_long() == 3
    # with a live solver: parsed under push/pop, the solver's own assertions untouched
    more = parse_smt2_string("(assert (= a #x04))")
    assert len(more) == 1 and len(s.assertions()) == 2
    s.close()


def test_frontend_refusals_are_parse_errors():
    """A script the frontend refuses (a wrong arity, a sort error, a constant that does not
    fit, a rejected command) is a ParseError with the solver as it was, not the end of the
    process."""
    tm = TermManager()
    s = Solver(tm)
    s.from_string("(declare-fun f ((_ BitVec 8)) (_ BitVec 8)) (declare-fun x () (_ BitVec 8)) "
                  "(assert (= (f x) x))")
    for script in ["(assert (= (f x x) x))", "(assert (= x #b1))", "(assert (= x (_ bv300 8)))",
                   "(declare-fun z () (_ BitVec 0))", "(set-option :produce-models maybe)",
                   "(assert (= x ((_ extract 9 2) x)))", "(assert (= x (bvadd x)))"]:
        with pytest.raises(ParseError):
            s.from_string(script)
        assert len(s.assertions()) == 1
    assert s.check() == sat
    s.close()


def test_stp_decorator_and_current_solver():
    @stp.stp
    def constraints(a, b=32):  # 2.x: a default gives the width of the fresh symbol
        c = a + b
        assert a > 3
        assert c == 20
        return c

    s = Solver()
    assert current_solver() is None
    with pytest.raises(StateError):
        constraints()
    with solver_scope(s):
        assert current_solver() is s
        c = constraints()
        assert isinstance(c, BitVecRef) and c.size() == 32
        assert check() == sat
        m = model()
        assert m[c].as_long() == 20 and m[BitVec("constraints_0_a", 32)].as_long() > 3
        x = BitVec("x", 8)
        add(x == 3)
        assert check() == sat and model()[x].as_long() == 3
        # explicit arguments are used in place of fresh symbols
        y = BitVec("y", 32)
        d = constraints(y, 10)
        assert check() == sat and model()[y].as_long() == 10 and model()[d].as_long() == 20
    assert current_solver() is None
    s.close()
    with pytest.raises(TypeError):
        solver_scope(3).__enter__()


def test_stp_decorator_keeps_the_2x_meanings():
    """The decorator exists for 2.x code, whose bit-vector operators were unsigned and
    logical: the comparisons and >> read their operands as unsigned, and / // % are the
    unsigned quotient and remainder (the z3-style operators elsewhere are signed)."""
    @stp.stp
    def big(x):
        assert x > 0x7fffffff

    @stp.stp
    def shr(x):
        assert (x >> 31) == 1

    @stp.stp
    def half(x):
        assert x == 0xfffffffe
        return x // 2

    @stp.stp
    def tenth(x):
        assert x == 0xfffffffe
        return x / 10

    @stp.stp
    def rest(x):
        assert x == 0xffffffff
        return x % 10

    for fn in (big, shr):
        s = Solver()
        with solver_scope(s):
            fn()
            assert check() == sat, fn.__name__
        s.close()
    s = Solver()
    with solver_scope(s):
        h, t, r = half(), tenth(), rest()
        assert check() == sat
        m = model()
        assert m[h].as_long() == 0x7fffffff and m[t].as_long() == 0xfffffffe // 10
        assert m[r].as_long() == 0xffffffff % 10
    s.close()


def test_close_and_lifetime():
    x = BitVec("x", 8)
    s = Solver()
    s.add(x == 1)
    assert s.check() == sat
    m = s.model()
    s.close()
    assert s.closed and repr(s) == "Solver(closed)"
    assert m[x].as_long() == 1  # the model outlives the solver
    for op in (s.check, s.model, lambda: s.add(x == 2), s.assertions, s.push, s.to_smt2):
        with pytest.raises(StateError):
            op()
    s.close()  # idempotent
    s.interrupt()  # harmless on a closed solver
    s2 = Solver()  # the manager serves new solvers as before
    assert s2.check() == sat
    del s2
    import gc
    gc.collect()
    s3 = Solver()  # a collected solver frees its slot too
    s3.close()


def test_a_solver_whose_options_were_touched_is_freed_at_once():
    # the cached options view holds the solver weakly: a strong reference back
    # made the solver cyclic garbage, freed only by the collector
    import gc
    import weakref
    gc.disable()
    try:
        s = Solver()
        s.set(max_time=1000)
        view = s.options
        assert view.get("max-time") is not None
        r = weakref.ref(s)
        del s
        assert r() is None
        with pytest.raises(StateError):
            view.get("max-time")
    finally:
        gc.enable()


def test_every_unsat_core_rechecks_unsat():
    # under the default options the driver engages after a push, and its
    # failed conjuncts map back to whole assumptions
    p, q, r = Bools("p q r")
    s = Solver()
    s.add(Or(Not(p), Not(q)))
    s.push()
    for _ in range(4):
        for assumptions in ([r, And(p, q)], [p, Not(p)], [r, Not(r), q]):
            assert s.check(*assumptions) == unsat
            core = s.unsat_core()
            assert len(core) > 0 and s.check(*core) == unsat
    s.close()


_HARD_SCRIPT = """
(declare-fun hx () (_ BitVec 64)) (declare-fun hy () (_ BitVec 64))
(assert (= (bvmul ((_ zero_extend 64) hx) ((_ zero_extend 64) hy)) (_ bv18446744073709551557 128)))
(assert (not (= hx (_ bv1 64)))) (assert (not (= hy (_ bv1 64)))) (assert (bvult hx hy))
(check-sat)
"""


def test_interrupt_reaches_a_check_the_script_runs():
    # interrupt() from another thread, and Ctrl-C on the main thread, stop a check an EXECUTE
    # script runs as they stop check(): the script ran on (to max_time) and the interrupt stayed
    # pending, spoiling the next check
    import signal
    import threading
    backend = interruptible_backend()
    if backend is None:
        pytest.skip("no backend of this build can be interrupted mid-search")
    s = Solver(tm=TermManager(), sat_backend=backend, max_time=120000)
    out = []
    s.set_output_sink(out.append)
    timer = threading.Timer(0.3, s.interrupt)
    timer.start()
    t0 = time.monotonic()
    s.from_string(_HARD_SCRIPT, mode="execute")
    timer.join()
    assert time.monotonic() - t0 < 60 and "".join(out) == "unknown\n" and not s.interrupt_pending()
    s.close()
    if threading.current_thread() is not threading.main_thread():
        return
    s = Solver(tm=TermManager(), sat_backend=backend, max_time=120000)
    timer = threading.Timer(0.3, signal.raise_signal, (signal.SIGINT,))
    timer.start()
    t0 = time.monotonic()
    with pytest.raises(KeyboardInterrupt):
        s.from_string(_HARD_SCRIPT, mode="execute")
    timer.join()
    assert time.monotonic() - t0 < 60 and not s.interrupt_pending()
    s.close()


def test_a_callback_that_calls_the_library_is_refused():
    # a sink that pushed tripped an assertion part way through a check-sat, and one that
    # parsed deadlocked on the parser lock: every call from a callback raises StateError now,
    # but interrupt(), clear_interrupt() and interrupt_pending()
    s = Solver(tm=TermManager())
    seen = []

    def sink(text):
        if not text or seen:
            return
        for call in (s.push, lambda: s.from_string("(declare-fun z () Bool)")):
            try:
                call()
                seen.append("called")
            except StateError:
                seen.append("refused")
        s.interrupt()
        s.clear_interrupt()
        seen.append(s.interrupt_pending())

    s.set_output_sink(sink)
    s.from_string("(declare-fun x () Bool) (assert x) (check-sat)", mode="execute")
    assert seen == ["refused", "refused", False]
    assert s.check() == sat
    s.close()


def test_a_busy_manager_refuses_other_threads_and_close_is_deferred():
    # A check releases the GIL: another thread building on the same manager entered the engine
    # under it (heap corruption, a failed assertion), and close() from another thread deleted the
    # solver under its own running check (a crash). The other thread now gets StateError, and
    # close() interrupts the check and deletes the solver once it returns.
    import threading
    backend = interruptible_backend()
    if backend is None:
        pytest.skip("no backend of this build can be interrupted mid-search")
    tm = TermManager()
    s = Solver(tm=tm, sat_backend=backend, max_time=120000)
    x, y = BitVecs("bx by", 64, tm=tm)
    s.add(ZeroExt(64, x) * ZeroExt(64, y) == 18446744073709551557, x != 1, y != 1, ULT(x, y))
    seen = []

    def build():
        time.sleep(0.2)
        try:
            BitVec("from_elsewhere", 8, tm=tm)
            seen.append("built")
        except StateError:
            seen.append("refused")
        s.close()
        seen.append("closed")

    other = threading.Thread(target=build)
    other.start()
    r = s.check()
    other.join()
    assert seen == ["refused", "closed"]
    assert r == unknown and r.reason == UnknownReason.INTERRUPTED
    assert s.closed
    BitVec("afterwards", 8, tm=tm)  # the manager is idle again, and usable from any thread
    stp._core.drain_releases()
    assert stp._core.pending_releases() == 0
