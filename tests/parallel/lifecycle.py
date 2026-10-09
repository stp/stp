#!/usr/bin/env python3
"""Process failures inside the group, against real forked processes.

stp-p -jN (N > 1) on QF_BV is a supervisor, the group's owner, the hedge it
forks once its parse has read the logic, and its roots, forked at ordinary
STP's before-search point. A stopped or killed root, or a killed hedge,
leaves the rest to answer (here: unknown at the deadline, on a formula nobody
decides in a second), and a death is in the stats; every root and the hedge
aborting is an error, as is a killed owner; a killed supervisor takes
everything with it. Nothing owned survives any of them. Then the deadline:
it covers parsing, an answer found before it is published, and an answer
that stdout cannot take is still the exit status. Arguments: stp-p,
stpp-drive."""
import ctypes
import os
import pathlib
import signal
import subprocess
import sys
import tempfile
import time

import sanitizer
binary = str(pathlib.Path(sys.argv[1]).resolve())
driver = [str(pathlib.Path(sys.argv[2]).resolve())]
sanitizer.install(binary, driver[0])
assert ctypes.CDLL(None).prctl(36, 1, 0, 0, 0) == 0  # subreaper for parent-death test
cpus = sorted(os.sched_getaffinity(0))
G = min(4, len(cpus))
probe = subprocess.run([binary, f'-j{G}'], input='(set-logic QF_BV)(check-sat)', text=True,
                       capture_output=True, timeout=30)
if G < 3 or (probe.returncode == 2 and 'clause-import' in probe.stderr):
    print(f'SKIP: the group needs three CPUs and clause import ({G} CPUs; {probe.stderr.strip()})')
    sys.exit(0)


def children(pid):
    try:
        return [int(x) for x in pathlib.Path(f'/proc/{pid}/task/{pid}/children').read_text().split()]
    except FileNotFoundError:
        return []


def name(pid):
    try:
        return pathlib.Path(f'/proc/{pid}/comm').read_text().strip()
    except FileNotFoundError:
        return ''


def tree(p):
    """supervisor -> owner -> {hedge, roots}, once all exist."""
    until = time.monotonic() + 10
    while time.monotonic() < until:
        owners = children(p.pid)
        if owners:
            group = children(owners[0])
            hedges = [c for c in group if name(c) == 'stp-p hedge']
            roots = [c for c in group if name(c) == 'stp-p root']
            if len(hedges) == 1 and len(roots) == G - 1:
                return {'owner': owners[0], 'hedge': hedges[0], 'roots': roots}
        assert p.poll() is None, ('early exit', p.communicate())
        time.sleep(.002)
    raise AssertionError('the group was not observed')


def gone(pids):
    until = time.monotonic() + 6
    while time.monotonic() < until:
        for pid in pids:
            try:
                os.waitpid(pid, os.WNOHANG)
            except ChildProcessError:
                pass
        if not any(pathlib.Path(f'/proc/{pid}').exists() for pid in pids):
            return
        time.sleep(.005)
    raise AssertionError(('owned processes survived', pids))


with tempfile.TemporaryDirectory(prefix='stpp-lifecycle-') as tmp:
    tmp = pathlib.Path(tmp)
    source = '(set-logic QF_BV)' + ''.join(f'(declare-const x{i} (_ BitVec 4))' for i in range(15))
    source += ''.join(f'(assert (bvult x{i} #xe))' for i in range(15))
    source += ''.join(f'(assert (not (= x{i} x{j})))' for i in range(15) for j in range(i))
    source += '(check-sat)'
    path = tmp/'pigeons.smt2'
    path.write_text(source)
    actions = ('stop-root', 'kill-root', 'kill-hedge', 'kill-owner', 'kill-parent', 'abort-all')
    for action in actions:
        stats = tmp/f'{action}.json'
        p = subprocess.Popen([binary, f'-j{G}', '--timeout', '2', '--stats-json', str(stats),
                              str(path)],
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        t = tree(p)
        owned = [t['owner'], t['hedge'], *t['roots']]
        if action == 'stop-root':
            os.kill(t['roots'][-1], signal.SIGSTOP)
        elif action == 'kill-root':
            os.kill(t['roots'][-1], signal.SIGABRT)
        elif action == 'kill-hedge':
            os.kill(t['hedge'], signal.SIGKILL)
        elif action == 'kill-owner':
            os.kill(t['owner'], signal.SIGKILL)
        elif action == 'abort-all':
            for pid in (*t['roots'], t['hedge']):
                os.kill(pid, signal.SIGABRT)
        else:
            os.kill(p.pid, signal.SIGKILL)
        out, err = p.communicate(timeout=10)
        if action in ('kill-owner', 'abort-all'):
            assert p.returncode == 2 and not out, (action, p.returncode, out, err)
        elif action == 'kill-parent':
            assert p.returncode == -signal.SIGKILL and not out
        else:
            assert (p.returncode, out) == (0, 'unknown\n'), (action, p.returncode, out, err)
        if action in ('kill-root', 'kill-hedge'):
            # The run timed out, but the death is in the stats.
            text = stats.read_text()
            death = '"failed": "signal 6"' if action == 'kill-root' else '"failed": "signal 9"'
            assert death in text, text[:2000]
            if action == 'kill-hedge':
                assert '"hedge": true' in text, text[:2000]
        gone(owned)
    # Without the hedge (the test driver), every root aborting is an error.
    p = subprocess.Popen([*driver, f'-j{G}', '--hedge', 'none', '--timeout', '5', str(path)],
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    until = time.monotonic() + 10
    roots = []
    while time.monotonic() < until and len(roots) < G:
        owners = children(p.pid)
        roots = children(owners[0]) if owners else []
        time.sleep(.002)
    assert len(roots) == G, roots
    for pid in roots:
        os.kill(pid, signal.SIGABRT)
    out, err = p.communicate(timeout=10)
    assert p.returncode == 2 and not out and 'every batch root failed' in err, (p.returncode, out, err)
    gone(roots)
    # Parsing and blocked output must not bypass the deadline.
    large = tmp/'large.smt2'
    large.write_text('(set-logic QF_BV)' + '(assert true)' * 200000 + '(check-sat)')
    p = subprocess.run([binary, f'-j{G}', '--timeout', '.01', str(large)], capture_output=True,
                       text=True, timeout=10)
    assert (p.returncode, p.stdout) == (0, 'unknown\n'), (p.returncode, p.stdout, p.stderr)
    # A stdout that cannot take the answer: the answer is still the exit
    # status, and stderr says the line was lost.
    readfd, writefd = os.pipe2(os.O_NONBLOCK)
    try:
        while True:
            os.write(writefd, b'x' * 4096)
    except BlockingIOError:
        pass
    p = subprocess.Popen([binary, '--timeout', '.1'], stdin=subprocess.PIPE, stdout=writefd,
                         stderr=subprocess.PIPE, text=True)
    _, err = p.communicate('(set-logic QF_BV)(assert true)(check-sat)', timeout=5)
    assert p.returncode in (10, 0) and 'was lost' in err, (p.returncode, err)
    os.close(readfd)
    os.close(writefd)
    # An answer a root found before the deadline is published, though the
    # group is still waiting for another (the driver's batch-all, root 1 held
    # back) when the deadline stops the run.
    fac = tmp/'factoring.smt2'
    fac.write_text('(set-logic QF_BV)(declare-const x (_ BitVec 40))(declare-const y (_ BitVec 40))'
                   f'(assert (= (bvmul x y) (_ bv{46337 * 46327} 40)))(assert (bvugt x (_ bv1 40)))'
                   '(assert (bvugt y (_ bv1 40)))(assert (bvult x (_ bv65536 40)))'
                   '(assert (bvult y (_ bv65536 40)))(check-sat)')
    stats = tmp/'deadline-answer.json'
    p = subprocess.run([*driver, f'-j{G}', '--control', 'batch-all', '--inject', 'hold-root=1',
                        '--timeout', '8', '--stats-json', str(stats), str(fac)],
                       capture_output=True, text=True, timeout=30)
    assert (p.returncode, p.stdout) == (10, 'sat\n'), (p.returncode, p.stdout, p.stderr)
    text = stats.read_text()
    assert '"decided": "sat"' in text or '"winner": "root"' in text, text[:2000]
print(f'PASS: {len(actions)} root/hedge/owner/parent failures, parsing deadline, '
      'an answer at the deadline, blocked publication')
