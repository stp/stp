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

"""Threads and signals (DESIGN.md section 9): interrupt() from another thread while a check
runs with the GIL released, Ctrl-C on the main thread, the thread pin of a manager, and the
deferred release of wrappers finalised off the manager's thread."""

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


def test_manager_is_pinned_to_its_thread(fresh_manager):
    x = BitVec("x", 8)
    s = Solver()
    s.add(x == 1)
    assert s.check() == sat
    m = s.model()
    errors = []

    def other():
        for op in (lambda: BitVec("y", 8), lambda: x + 1, lambda: s.check(), lambda: m[x], lambda: s.add(x == 2),
                   lambda: fresh_manager.declare("q", BitVecSort(8))):
            try:
                op()
                errors.append(None)
            except Exception as e:  # noqa: BLE001
                errors.append(e)

    t = threading.Thread(target=other)
    t.start()
    t.join()
    assert len(errors) == 6 and all(isinstance(e, StateError) for e in errors)
    assert all("pin" in str(e) for e in errors)  # the Python pin ("pinned") or the C++ core's own ("pins")
    assert s.check() == sat and m[x].as_long() == 1  # nothing was touched
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
    """DESIGN.md section 9: independent managers are fully concurrent. Run in a subprocess
    because the failure is a glibc abort, which no test framework survives."""
    r = subprocess.run([sys.executable, "-c", _TWO_MANAGERS_TWO_THREADS], capture_output=True, text=True, timeout=120)
    assert r.returncode == 0 and "worker ok" in r.stdout and "main ok" in r.stdout, (r.returncode, r.stdout, r.stderr[-400:])


def test_deferred_release_from_another_thread(fresh_manager):
    holder = [BitVec("dropme", 8) + 1, Solver()]
    holder[1].add(holder[0] == 2)
    assert holder[1].check() == sat
    holder.append(holder[1].model())
    _core.drain_releases()
    before = _core.pending_releases()

    def drop():
        holder.clear()
        gc.collect()

    t = threading.Thread(target=drop)
    t.start()
    t.join()
    # the wrappers died on the other thread: their handles wait on the queue
    assert _core.pending_releases() > before
    BitVec("touch", 8)  # an entry point on the owning thread drains it
    assert _core.pending_releases() == 0
    s = Solver()  # the solver slot is free again
    assert s.check() == sat
    s.close()


def test_solver_use_from_another_thread_is_refused(fresh_manager):
    s = Solver()
    x = BitVec("x", 8)
    s.add(x == 1)
    seen = []

    def other():
        try:
            s.check()
        except StateError as e:
            seen.append(e)

    t = threading.Thread(target=other)
    t.start()
    t.join()
    assert len(seen) == 1
    assert s.check() == sat
    s.close()
