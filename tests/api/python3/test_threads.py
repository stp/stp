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

"""Threads and signals: interrupt() from another thread while a check
runs with the GIL released, Ctrl-C on the main thread, a manager used from several threads one
call at a time, and the deferred release of wrappers finalised while their manager is busy."""

import gc
import os
import signal
import subprocess
import sys
import threading
import time

import pytest

from stp import *
import stp
from stp import _core


def test_interrupt_from_another_thread(hard):
    fired = []

    def other():
        time.sleep(0.4)
        hard.interrupt()  # the one call allowed from any thread
        fired.append(True)

    t = threading.Thread(target=other)
    t.start()
    t0 = time.monotonic()
    r = hard.check()
    elapsed = time.monotonic() - t0
    t.join()
    assert fired and r == unknown and r.reason == UnknownReason.INTERRUPTED and r.reason == "interrupted"
    assert elapsed < 60 and "interrupt" in r.reason_message
    assert not hard.interrupt_pending()  # consumed by the check that reported it
    assert hard.reason_unknown() == UnknownReason.INTERRUPTED


def test_pending_interrupt(hard):
    hard.interrupt()
    assert hard.interrupt_pending()
    hard.clear_interrupt()
    assert not hard.interrupt_pending()
    hard.interrupt()
    r = hard.check()
    assert r == unknown and r.reason == UnknownReason.INTERRUPTED
    assert not hard.interrupt_pending()


def test_sigint_on_main_thread(hard):
    assert threading.current_thread() is threading.main_thread()
    before = signal.getsignal(signal.SIGINT)

    def kill():
        time.sleep(0.4)
        os.kill(os.getpid(), signal.SIGINT)

    t = threading.Thread(target=kill)
    t.start()
    t0 = time.monotonic()
    with pytest.raises(KeyboardInterrupt):
        hard.check()
    elapsed = time.monotonic() - t0
    t.join()
    assert elapsed < 60
    assert signal.getsignal(signal.SIGINT) is before  # Python's handler is back
    assert hard.check(timeout=0).reason == UnknownReason.TIMEOUT  # the solver is usable


def test_manager_usable_from_another_thread(fresh_manager):
    """A manager and everything created from it may be used from any thread, one call at a
    time; the caller serialises (here: the join before the next use)."""
    x = BitVec("x", 8)
    s = Solver()
    s.add(x == 1)
    assert s.check() == sat
    m = s.model()
    results = []

    def other():
        y = BitVec("y", 8)
        s.add(y == x + 1)
        results.append(s.check())
        results.append(s.model()[y].as_long())
        results.append(m[x].as_long())
        results.append(fresh_manager.declare("q", BitVecSort(8)) is not None)

    t = threading.Thread(target=other)
    t.start()
    t.join()
    assert results == [sat, 2, 1, True]
    assert s.check() == sat and s.model()[x].as_long() == 1 and m[x].as_long() == 1
    s.close()


def test_manager_handed_from_thread_to_thread(fresh_manager):
    """Declared here, asserted and checked on a second thread, read on a third: every theory's
    engine state is exercised off the creating thread."""
    x = BitVec("x", 8)
    fx = FP("fx", Float32())
    r = Real("r")
    f = Function("f", BitVecSort(8), BitVecSort(8))
    a = Array("a", BitVecSort(8), BitVecSort(8))
    half = FPVal(1.5, Float32())
    s = Solver()
    failures = []

    def second():
        try:
            s.add(x == 5, fx == half, r + 1 < RealVal("3/2"), f(x) == 7, a[x] == 9)
            if s.check() != sat:
                failures.append("the check did not answer sat")
        except Exception as e:  # noqa: BLE001
            failures.append(repr(e))

    t = threading.Thread(target=second)
    t.start()
    t.join()
    assert not failures, failures
    values = []

    def third():
        try:
            m = s.model()
            values.append(m[x].as_long())
            values.append(m.eval(f(x)).as_long())
            values.append(m.eval(a[x]).as_long())
            values.append(m.eval(r).as_fraction() < 0.5)
            values.append(m.eval(fx).eq(half))
        except Exception as e:  # noqa: BLE001
            failures.append(repr(e))

    t = threading.Thread(target=third)
    t.start()
    t.join()
    assert not failures, failures
    assert values == [5, 7, 9, True, True]
    assert s.model()[x].as_long() == 5  # and back here
    s.close()


_TWO_MANAGERS_TWO_THREADS = '''
import threading, stp
tm1 = stp.TermManager()
def other():
    tm2 = stp.TermManager()
    z = stp.BitVec("z", 8, tm=tm2)
    v = tm2.mk_bv(8, 3)
    s = stp.Solver(tm2); s.add(z == v); assert s.check() == stp.sat and s.model()[z].as_long() == 3
    print("worker ok", flush=True)
t = threading.Thread(target=other); t.start(); t.join()
print("main ok", flush=True)
'''


def test_independent_managers_on_two_threads():
    """Independent managers are fully concurrent. Run in a subprocess
    because the failure is a glibc abort, which no test framework survives."""
    r = subprocess.run([sys.executable, "-c", _TWO_MANAGERS_TWO_THREADS], capture_output=True, text=True, timeout=120)
    assert r.returncode == 0 and "worker ok" in r.stdout and "main ok" in r.stdout, (r.returncode, r.stdout, r.stderr[-400:])


def test_release_from_another_thread_while_idle(fresh_manager):
    holder = [BitVec("dropme", 8) + 1, Solver()]
    holder[1].add(holder[0] == 2)
    assert holder[1].check() == sat
    holder.append(holder[1].model())
    gc.collect()  # earlier tests' cyclic garbage, whose managers are gone, must not count below
    _core.drain_releases()
    before = _core.pending_releases()

    def drop():
        holder.clear()
        gc.collect()

    t = threading.Thread(target=drop)
    t.start()
    t.join()
    # the manager was idle: the wrappers' handles were released on the spot
    assert _core.pending_releases() == before
    s = Solver()
    assert s.check() == sat
    s.close()


def test_release_during_a_check_is_deferred(hard):
    tm = hard.manager()
    holder = [BitVec("dropped_during_check", 8, tm=tm) + 1]
    _core.drain_releases()
    before = _core.pending_releases()

    def other():
        time.sleep(0.4)
        holder.clear()  # the manager is busy on the main thread: the finaliser must not touch it
        gc.collect()
        hard.interrupt()

    t = threading.Thread(target=other)
    t.start()
    r = hard.check()
    t.join()
    assert r == unknown and r.reason == UnknownReason.INTERRUPTED
    assert _core.pending_releases() > before  # queued: its manager was busy
    BitVec("touch", 8, tm=tm)  # any entry point, on any thread, drains it once the manager is idle
    assert _core.pending_releases() == before


def test_solver_use_from_another_thread_works(fresh_manager):
    s = Solver()
    x = BitVec("x", 8)
    s.add(x == 1)
    seen = []

    def other():
        seen.append(s.check())
        seen.append(s.model()[x].as_long())

    t = threading.Thread(target=other)
    t.start()
    t.join()
    assert seen == [sat, 1]
    assert s.check() == sat
    s.close()
