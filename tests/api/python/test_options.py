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

"""Options: kwargs, the Options object, python_key spellings, typed values, the live view
of a solver and its timing rules, introspection."""

import datetime

import pytest

from stp import *
import stp


def test_options_object():
    o = Options(max_time=500, produce_models=True, random_seed=3)
    assert o["max-time"] == 500 and o["max_time"] == 500 and o["timeout"] == 500
    assert o["produce_models"] is True and o["random-seed"] == 3
    assert o.is_set("max_time") and not o.is_set("logic") and o["logic"] == "" and o.get("logic") == ""
    assert "max_time" in o and "max-time" in o and "timeout" in o and "no_such" not in o and 3 not in o
    assert len(o) == len(list(o)) > 200 and "max-time" in o.keys() and ("max-time", 500) in o.items()
    assert not o.live
    assert o.resolved("produce-models") is True
    o.set("max-time", 250)
    assert o["max_time"] == 250
    o.set("max-time", 100, "random-seed", 9)
    assert o["max_time"] == 100 and o["random_seed"] == 9
    o.set({"max_time": 50})
    assert o["max_time"] == 50
    with pytest.raises(TypeError):
        o.set("max-time")
    o["timeout"] = 60
    assert o["max_time"] == 60
    o2 = o.copy()
    o2["max_time"] = 70
    assert o["max_time"] == 60 and o2["max_time"] == 70 and o != o2 and o == o.copy()
    o.reset("max_time")
    assert o["max_time"] is None and not o.is_set("max_time")
    o.reset()
    assert not o.is_set("random_seed") and repr(o) == "Options()"
    assert "max_time=" in repr(Options(max_time=5)) and "OptionInfo" in repr(o.info("max-time"))
    o.resolve()
    assert Options.names(Tier.STABLE) == Options.names(0) and len(Options.names()) > len(Options.names(Tier.STABLE))
    assert "sat-backend" in Options.help(Tier.STABLE) and len(Options.help()) > len(Options.help(Tier.STABLE))


def test_option_errors():
    o = Options()
    with pytest.raises(UnknownOption) as e:
        o["no_such"] = 1
    assert isinstance(e.value, KeyError) and e.value.option == "no_such"
    with pytest.raises(UnknownOption):
        o["no_such"]
    with pytest.raises(UnknownOption):
        o.info("no_such")
    with pytest.raises(UnknownOption):
        Options(no_such=1)
    with pytest.raises(TypeError):
        o[3] = 1
    for key, value in (("max_time", True), ("produce_models", 5), ("random_seed", 1.5), ("random_seed", -1),
                       ("max_time", -5), ("max_time", "500"), ("produce_models", "maybe"), ("sat_backend", 3),
                       ("logic", None), ("max_num_confl", "lots")):
        with pytest.raises(OptionError) as e:
            o[key] = value
        assert e.value.code in (ErrorCode.OPTION_VALUE, ErrorCode.OPTION_UNAVAILABLE), key
        assert isinstance(e.value, ValueError) and not isinstance(e.value, KeyError)
    with pytest.raises(OptionError):
        o.set_args("--max-time=500")  # durations need a unit here
    with pytest.raises(OptionError):
        Options(max_time=5, logic="QF_BV", simplify=False).set_args("--no-such-flag")


def test_typed_values():
    o = Options()
    o["max_time"] = 1500
    assert o["max_time"] == 1500 and o.info("max_time").current == 1500
    o["max_time"] = datetime.timedelta(seconds=2.5)
    assert o["max_time"] == 2500
    o["max_time"] = "250ms"
    assert o["max_time"] == 250
    o["max_time"] = "1.5s"
    assert o["max_time"] == 1500
    o["max_time"] = 2.0
    assert o["max_time"] == 2
    o["max_time"] = None
    assert o["max_time"] is None
    o["incremental"] = True
    assert o["incremental"] == "on"
    o["incremental"] = False
    assert o["incremental"] == "off"
    o["incremental"] = "auto"
    assert o["incremental"] == "auto"
    with pytest.raises(OptionError):
        o["incremental"] = "sometimes"
    o["cnf_generation_effort"] = "high"
    assert o["cnf-generation-effort"] == "high"
    o["sat_backend"] = "cadical" if has_sat_backend("cadical") else "cryptominisat"
    assert o["sat-backend"] in sat_backends()
    o["bb_div_v3"] = False
    assert o["bb.div-v3"] is False
    o.set_args("--fp-abstraction", "--max-time=2s", "--bb.div-v3=true")
    assert o["fp_abstraction"] is True and o["max_time"] == 2000 and o["bb.div-v3"] is True
    o.set_args(["--random-seed=4"])
    assert o["random_seed"] == 4
    o["default_rounding_mode"] = RoundingMode.RTZ
    assert o["default-rounding-mode"] == "RTZ"
    info = o.info("fp-abstraction-ops")
    if info.type == "set":
        o["fp_abstraction_ops"] = ["add", "mul"]
        assert set(o["fp-abstraction-ops"]) == {"add", "mul"}


def test_option_info():
    o = Options(max_time=500)
    i = o.info("max_time")
    assert isinstance(i, OptionInfo) and i.name == "max-time" and i.python_key == "max_time" and i.type == "duration"
    assert i.default is None and i.current == 500 and i.is_set is True and i.tier == Tier.STABLE
    assert i.settable == "anytime" and i.scope == "solver" and i.category == "limits" and i.help
    assert i.supported is True and "max_time" in i.aliases and i.short == "k" and i.negation == ""
    j = o.info("uf_sort_width")
    assert j.type == "uint" and j.min == 1 and j.max == 1024 and j.default == 16 and j.scope == "manager" and j.settable == "construction"
    k = o.info("sat-backend")
    assert k.type == "enum" and "cadical" in k.values and k.default == "auto" and k.settable == "construction"
    assert o.info("logic").settable == "before-first-check" and o.info("incremental").type == "mode"
    assert o.info("simplify").scope == "manager" and o.info("simplify").default is True
    assert o.info("bb.div-v3").tier == Tier.EXPERIMENTAL and o.info("bb.div-v3").python_key == "bb_div_v3"
    assert o.info("print-counterex").tier == Tier.DIAGNOSTIC
    assert Option.MAX_TIME.name == "MAX_TIME" and Options.names(Tier.STABLE)[Option.MAX_TIME] == "max-time"


def test_solver_options_live_view():
    s = Solver(max_time=500, random_seed=7, bb_div_v3=False)
    o = s.options
    assert o.live and o["max_time"] == 500 and o["random_seed"] == 7 and o["bb.div-v3"] is False
    assert s.options is o
    s.set(logic="QF_BV")
    assert o["logic"] == "QF_BV" and o.info("logic").current == "QF_BV" and o.is_set("logic")
    s.set("max-time", 700)
    assert o["max_time"] == 700
    s.set_args("--max-time=1s")
    assert o["timeout"] == 1000
    o["max_time"] = 300
    assert s.options["max_time"] == 300
    with pytest.raises(UnknownOption):
        s.set(no_such=1)
    with pytest.raises(OptionError):
        s.set(max_time=True)
    with pytest.raises(OptionError) as e:
        s.set(sat_backend="cadical")  # construction-only: OPTION_TIMING on a live solver
    assert e.value.code == ErrorCode.OPTION_TIMING and e.value.option == "sat-backend"
    with pytest.raises(OptionError) as e:
        s.set(simplify=False)  # manager-scoped
    assert e.value.code == ErrorCode.OPTION_VALUE and e.value.option == "simplify"
    x = BitVec("x", 8)
    s.add(x == 1)
    assert s.check() == sat
    with pytest.raises(OptionError) as e:
        s.set(logic="QF_ABV")  # before-first-check: refused after a check, unchanged
    assert e.value.code == ErrorCode.OPTION_TIMING and o["logic"] == "QF_BV"
    s.set(max_time=1000)  # anytime
    assert o["max_time"] == 1000 and s.check() == sat
    o["max_time"] = None  # no limit, read back through the millisecond getter
    assert o["max_time"] is None and o.is_set("max_time") and s.check() == sat
    o.reset("max_time")
    assert o["max_time"] is None
    detached = o.copy()
    assert not detached.live and detached["logic"] == "QF_BV" and detached["random_seed"] == 7
    detached["logic"] = "QF_ABV"
    assert o["logic"] == "QF_BV"
    assert o.info("logic").is_set and not o.info("produce_models").is_set
    s.close()
    s2 = Solver(options=detached)
    assert s2.options["logic"] == "QF_ABV" and s2.options["random_seed"] == 7
    s2.close()
    s3 = Solver(options={"max_time": 5, "logic": "QF_BV"}, random_seed=2)
    assert s3.options["max_time"] == 5 and s3.options["random_seed"] == 2
    s3.close()


def test_manager_scoped_options():
    with pytest.raises(OptionError) as e:
        Solver(simplify=False)
    assert e.value.option == "simplify" and "manager" in str(e.value)
    with pytest.raises(OptionError):
        Solver(uf_sort_width=8)
    tm = TermManager(options=Options(simplify=False, default_rounding_mode="RTZ", uf_sort_width=8))
    assert tm.simplify is False and tm.default_rounding_mode == RoundingMode.RTZ and tm.uf_sort_width == 8
    x = BitVec("x", 8, tm=tm)
    assert (x + 0).kind() == Kind.BV_ADD  # no construction-time folding
    assert (BitVec("x", 8) + 0).kind() == Kind.CONSTANT  # the default manager folds


def test_unavailable_backend():
    o = Options()
    with pytest.raises(OptionError) as e:
        o["sat_backend"] = "no-such-backend"
    assert e.value.code in (ErrorCode.OPTION_VALUE, ErrorCode.OPTION_UNAVAILABLE)
    missing = [b for b in ("cryptominisat", "cadical", "minisat", "simplifying-minisat") if not has_sat_backend(b)]
    if missing:
        o = Options(sat_backend=missing[0])  # a legal name: accepted by the value, refused by this build
        with pytest.raises(OptionError) as e:
            Solver(options=o)
        assert e.value.code == ErrorCode.OPTION_UNAVAILABLE and e.value.option == "sat-backend"
        assert missing[0] in str(e.value)


def test_a_live_reset_is_all_or_nothing_and_a_live_resolve_asks():
    # reset() of a solver's live options is the solver's reset_all: every
    # entry back to its default, or none when one whose window has closed
    # holds anything else; resolve() finds a conflict the writes allowed
    s = Solver()
    o = s.options
    o["end_after_cnf"] = True
    o["stop_after_cnf"] = True
    with pytest.raises(OptionError) as e:
        o.resolve()
    assert e.value.code == ErrorCode.OPTION_CONFLICT
    o.reset()
    assert not o.is_set("end_after_cnf") and not o.is_set("stop_after_cnf")
    o.resolve()
    o["random_seed"] = 7
    o["max_time"] = 500
    assert s.check() == sat
    with pytest.raises(OptionError) as e:
        o.reset()
    assert e.value.code == ErrorCode.OPTION_TIMING
    assert o["random_seed"] == 7 and o["max_time"] == 500
    s.close()
