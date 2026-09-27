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
from conftest import hard_solver


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
    cvc = s.to_string("cvc")
    assert "BITVECTOR(8)" in cvc and "ASSERT" in cvc
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
    # from_file with format detection, and the other input languages
    path = tmp_path / "q.smt2"
    path.write_text(s.to_smt2(with_check_sat=True))
    s3 = Solver(TermManager())
    s3.from_file(str(path))
    assert s3.check() == sat
    s3.close()
    s4 = Solver(TermManager())
    s4.from_string("x : BITVECTOR(8); ASSERT(x = 0hex05); QUERY(FALSE);", format="cvc")
    assert s4.check() == sat and s4.model()[s4.symbol("x")].as_long() == 5
    with pytest.raises(ArgumentError):
        s4.from_string("(assert true)", format="pdf")
    s4.close()
    # execute mode writes get-model responses to the diagnostic sink
    s5 = Solver(TermManager())
    out = []
    s5.set_diagnostic_sink(out.append)
    s5.from_string("(declare-fun z () Bool) (assert z) (check-sat) (get-model)", execute=True)
    assert s5.check() == sat
    s5.set_diagnostic_sink(None)
    s5.close()
    s.close()


def test_write_cnf(tmp_path):
    x, y = BitVecs("x y", 8)
    s = Solver()
    s.add(x + y == 3, ULT(x, y))
    path = tmp_path / "out.cnf"
    s.write_cnf(path)
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
    # with a live solver on the manager the formulas are solved in a scratch manager
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
    s2 = Solver()  # the manager is free again
    assert s2.check() == sat
    del s2
    import gc
    gc.collect()
    s3 = Solver()  # a collected solver frees its slot too
    s3.close()
