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

"""The library-level surface: version, capabilities, backends, the result and entry classes,
and the file variant of the script parser."""

import re

import pytest

from stp import *
import stp


def test_version_and_capabilities():
    v = version()
    assert isinstance(v, Version) and isinstance(v.major, int) and isinstance(v.minor, int) and isinstance(v.patch, int)
    assert v.string and str(v) == v.string == stp.__version__ and "%d.%d" % (v.major, v.minor) in v.string
    assert isinstance(v.git_sha, str) and isinstance(v.git_tag, str) and isinstance(v.build_info, str)
    assert "Version(" in repr(v)
    caps = capabilities()
    assert isinstance(caps, dict) and caps["api.version"] == "3.0.0-alpha"
    assert caps["array.const-equality"] is True and isinstance(caps["sat.backends"], (list, str))
    assert stp.capability("api.version") == "3.0.0-alpha" and stp.capability("no.such.key") is None
    backends = sat_backends()
    assert backends and all(has_sat_backend(b) for b in backends) and not has_sat_backend("no-such-backend")
    assert stp.get_internal_error_policy() is False  # poison, not abort


def test_result_classes():
    assert isinstance(sat, CheckSatResult) and isinstance(unsat, CheckSatResult) and isinstance(unknown, CheckSatResult)
    assert isinstance(valid, EntailmentResult) and isinstance(invalid, EntailmentResult)
    r = CheckSatResult(3, 1, "the time budget expired")
    assert r == unknown and r.reason == UnknownReason.TIMEOUT and r.reason_message == "the time budget expired"
    assert repr(r) == "unknown (timeout)" and r != sat and r == valid.__class__(3) and len({sat, unsat, unknown}) == 3
    e = EntailmentResult(3, 3)
    assert e.is_unknown() and e == unknown and e.reason == "interrupted" and repr(e) == "unknown (interrupted)"
    assert valid != invalid and hash(valid) != hash(invalid) and (valid == 1) is False


def test_sort_and_entry_base_classes():
    for s in (BoolSort(), BitVecSort(8), Float32(), RoundingModeSort(), RealSort(),
              ArraySort(BitVecSort(8), BitVecSort(8)), FuncSort(BitVecSort(8), BoolSort()), DeclareSort("S")):
        assert isinstance(s, SortRef) and s.kind() in SortKind and s.manager() is main_tm() and s.id >= 0
        assert re.match(r"\w+\(.*\)|\w+", repr(s))
    assert BoolSort().id >= 1  # sort ids are 1-based; 0 is never a sort id
    assert len({s.id for s in (BoolSort(), BitVecSort(8), Float32(), RealSort())}) == 4
    f = Function("f", BitVecSort(8), BitVecSort(8))
    x = BitVec("x", 8)
    s = Solver()
    s.add(f(x) == 3, x == 1)
    assert s.check() == sat
    entry = s.model()[f].entry(0)
    assert isinstance(entry, FuncEntry) and entry.num_args() == 1 and entry.value().as_long() == 3
    assert entry.arg_value(0).as_long() == 1 and entry.as_tuple() == ((entry.arg_value(0),), entry.value())
    assert "3" in repr(entry)
    s.close()


def test_parse_smt2_file(tmp_path):
    path = tmp_path / "in.smt2"
    path.write_text("(set-logic QF_BV)\n(declare-fun a () (_ BitVec 8))\n(assert (= a #x2a))\n(check-sat)\n")
    fs = parse_smt2_file(str(path))
    assert len(fs) >= 1 and all(isinstance(f, BoolRef) for f in fs)
    s = Solver()
    s.add(*fs)
    assert s.check() == sat and s.model()[BitVec("a", 8)].as_long() == 0x2A
    s.close()
    with pytest.raises(OSError):
        parse_smt2_file(str(tmp_path / "missing.smt2"))
