#!/usr/bin/env python3
"""Exercise the opt-in production coordinator within a four-CPU CI budget."""
import ctypes
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time

import sanitizer

binary, driver = map(lambda p: str(Path(p).resolve()), sys.argv[1:3])
sanitizer.install(binary, driver)
cpus = sorted(os.sched_getaffinity(0))[:4]
if len(cpus) < 4:
    print('SKIP: encoding groups need four allowed CPUs')
    sys.exit(0)
os.sched_setaffinity(0, cpus)
assert ctypes.CDLL(None).prctl(36, 1, 0, 0, 0) == 0
probe = subprocess.run([binary, '-j2'], input='(set-logic QF_BV)(check-sat)',
                       capture_output=True, text=True, timeout=10)
if probe.returncode == 2 and 'clause-import' in probe.stderr:
    print('SKIP: encoding groups need clause import')
    sys.exit(0)


def children(pid):
    try:
        return [int(p) for p in Path(f'/proc/{pid}/task/{pid}/children').read_text().split()]
    except FileNotFoundError:
        return []


def clean():
    until = time.monotonic() + 5
    while time.monotonic() < until:
        try:
            while os.waitpid(-1, os.WNOHANG)[0]:
                pass
        except ChildProcessError:
            pass
        if not children(os.getpid()):
            return
        time.sleep(.002)
    raise AssertionError(('unreaped descendants', children(os.getpid())))


def factoring(product):
    return ('(set-logic QF_BV)(declare-const x (_ BitVec 16))'
            '(declare-const y (_ BitVec 16))'
            f'(assert (= (bvmul x y) (_ bv{product} 16)))'
            '(assert (bvugt x #x0001))(assert (bvugt y #x0001))'
            '(assert (bvult x #x0100))(assert (bvult y #x0100))(check-sat)')


sat = factoring(101 * 103)
with tempfile.TemporaryDirectory(prefix='stpp-encoding-') as temporary:
    stats = Path(temporary) / 'stats.json'

    def run(program, body, answer, extra=(), grouped=True):
        args = [program, '-j4', '--stats-json', str(stats)]
        if '--timeout' not in extra:
            args.extend(['--timeout', '10'])
        if grouped:
            args.append('--encoding-groups')
        p = subprocess.run([*args, *extra], input=body, text=True,
                           capture_output=True, timeout=15)
        assert (p.returncode, p.stdout.strip()) == (
            {'sat': 10, 'unsat': 20, 'unknown': 0}[answer], answer), p
        report = json.loads(stats.read_text())
        assert report['cleanup_complete'], report
        clean()
        return report

    # Both real encodings, and the unchanged default, on SAT and UNSAT.
    for body, answer in [(sat, 'sat'), (factoring(10007), 'unsat')]:
        report = run(binary, body, answer)
        assert report['engine'] == 'encoding-groups', report
        assert report['groups_cleanup_complete'], report
        assert report['requested_jobs'] == 4, report
        assert [g['config'] for g in report['groups']] == ['default', 'cnf-gia-high']
        assert [g['slots'] for g in report['groups']] == [2, 2]
        for i, group in enumerate(report['groups']):
            inner = group.get('report') or {}
            if inner.get('engine') == 'batch-group':
                assert inner['parsed_query_reused'] and inner['parse_s'] == 0, inner
                if i:
                    assert not (inner.get('hedge') or {}).get('forked'), inner
        report = run(binary, body, answer, grouped=False)
        assert report['engine'] == 'batch-group', report

    # One parse and the ordinary route for other supported or unnamed logics.
    for body, answer in [
        (sat.replace('(set-logic QF_BV)', ''), 'sat'),
        ('(set-logic QF_FP)(declare-const x (_ FloatingPoint 5 11))'
         '(assert (fp.isNaN x))(assert (fp.eq x x))(check-sat)', 'unsat'),
        ('(set-logic QF_ABV)(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))'
         '(assert (= (select a #x00) #x01))(check-sat)', 'sat')]:
        report = run(binary, body, answer)
        assert report['engine'] == 'batch-group' and report['parsed_query_reused'], report

    # Failure and abrupt owner death both reclaim the failed group's budget.
    # Hold the survivor so the replacement, with its own seed, must decide.
    for failed, survivor in [('cnf-gia-high', 'default'), ('default', 'cnf-gia-high')]:
        for fault in ['fail', 'crash']:
            report = run(driver, sat, 'sat', ['--inject',
                         f'{fault}-encoding={failed},hold-encoding={survivor}'])
            assert report['recovery']['config'] == survivor, report
            assert report['recovery']['slots'] == 2 and report['winner_group'] == 2, report
            assert report['groups_cleanup_complete'], report

    # Cancellation starts from the decision note, before the winner exits.
    report = run(driver, sat, 'sat', ['--inject',
                 'hold-encoding=cnf-gia-high,linger-encoding=default'])
    default, gia = report['groups']
    assert report['winner_group'] == 0 and gia['cancelled'], report
    assert 0 < gia['stop_requested_at'] < default['ended_at'], report
    assert not gia['forced_stop'], report

    report = run(driver, sat, 'sat', ['--inject', 'unresponsive-encoding=cnf-gia-high'])
    assert report['groups'][1]['forced_stop'] and report['groups_cleanup_complete'], report

    report = run(driver, sat, 'sat', ['--inject', 'fork-fails'])
    assert report['engine'] == 'batch-group' and report['encoding_groups_fallback'], report

    for args in [['-j1'], ['-j3'], ['-j4', '--config', 'eager-arrays']]:
        p = subprocess.run([binary, '--encoding-groups', *args], input=sat,
                           capture_output=True, text=True, timeout=10)
        assert p.returncode == 2 and '--encoding-groups' in p.stderr, p

    p = subprocess.run([binary, '-j4', '--encoding-groups'],
                       input='(set-logic QF_BV)(check-sat)(check-sat)',
                       capture_output=True, text=True, timeout=10)
    assert p.returncode == 2 and not p.stdout.strip(), p
    clean()

    # Whole-tree timeout and user signal while both encoding owners are live.
    hold = 'hold-encoding=default,hold-encoding=cnf-gia-high'
    run(driver, sat, 'unknown', ['--inject', hold, '--timeout', '.1'])
    p = subprocess.Popen([driver, '-j4', '--encoding-groups', '--inject', hold],
                         stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                         text=True)
    p.stdin.write(sat)
    p.stdin.close()
    until = time.monotonic() + 5
    while time.monotonic() < until:
        owners = children(p.pid)
        if owners and len(children(owners[0])) >= 2:
            break
        time.sleep(.002)
    else:
        p.kill()
        raise AssertionError('encoding owners did not start')
    p.send_signal(signal.SIGTERM)
    assert p.wait(timeout=8) == 128 + signal.SIGTERM
    clean()

print('PASS: opt-in encoding groups, recovery, early cancellation and cleanup')
