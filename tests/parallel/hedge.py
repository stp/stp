#!/usr/bin/env python3
"""The hedge: the incremental driver from the first check, one plain check of
the query. Alone (the test driver's --config retained), as a portfolio side,
and beside the group, it must answer as ordinary STP does. Beside the group
it is forked by the group's owner once the owner's parse has read the logic,
and only on QF_BV: it asserts the terms the owner parsed, and on any other
logic there is no hedge. Arguments: stp-p, stpp-drive."""
import ctypes, json, os
from pathlib import Path
import subprocess, sys, tempfile, time
import sanitizer
binary = str(Path(sys.argv[1]).resolve())
driver = [str(Path(sys.argv[2]).resolve())]
sanitizer.install(binary, driver[0])
assert ctypes.CDLL(None).prctl(36, 1, 0, 0, 0) == 0
os.sched_setaffinity(0, set(sorted(os.sched_getaffinity(0))[:4]))
cpus = len(os.sched_getaffinity(0))
probe = subprocess.run([binary, '-j2'], input='(set-logic QF_BV)(check-sat)', text=True,
                       capture_output=True, timeout=30)
group = cpus >= 3 and not (probe.returncode == 2 and 'clause-import' in probe.stderr)


def children(pid):
    try:
        return [int(x) for x in Path(f'/proc/{pid}/task/{pid}/children').read_text().split()]
    except FileNotFoundError:
        return []


def clean():
    until = time.monotonic() + 5
    while time.monotonic() < until:
        while True:
            try:
                pid, _ = os.waitpid(-1, os.WNOHANG)
            except ChildProcessError:
                break
            if not pid:
                break
        if not children(os.getpid()):
            return
        time.sleep(.002)
    raise AssertionError(('owned processes remain', children(os.getpid())))


def retained_reports(stats):
    """The retained route's report inside a stats file: a portfolio's side,
    the group's hedge, or the route alone."""
    if 'sides' in stats:
        return [s['report'] for s in stats['sides'] if s['role'] == 'retained-root']
    if stats.get('engine') == 'batch-group':
        return [stats['hedge']['report']] if stats['hedge'].get('report') else []
    return [stats]


code = {'sat': 10, 'unsat': 20}
fixtures = [('(assert true)', 'sat'), ('(assert false)', 'unsat'),
            ('(declare-const x (_ BitVec 8))(declare-const y (_ BitVec 8))'
             '(assert (= (bvmul x y) #x0f))(assert (bvugt x #x01))', 'sat'),
            ('(declare-const x (_ BitVec 8))(declare-const y (_ BitVec 8))'
             '(assert (bvult x y))(assert (bvult y x))', 'unsat'),
            ('(declare-const x (_ BitVec 12))(declare-const y (_ BitVec 12))'
             '(assert (= (bvmul x y) #x0ff))(assert (bvugt x #x001))'
             '(assert (bvugt y #x001))(assert (distinct x y))', 'sat')]
modes = [[*driver, '-j1', '--config', 'retained'],
         [*driver, '-j2', '--portfolio', 'default,retained']]
if group:
    modes.append([binary, f'-j{min(4, cpus)}'])
records = []
with tempfile.TemporaryDirectory(prefix='stpp-hedge-') as temp:
    temp = Path(temp)
    for i, (body, expected) in enumerate(fixtures):
        path = temp / f'{i}.smt2'
        path.write_text('(set-logic QF_BV)' + body + '(check-sat)')
        for mode in modes:
            stats = temp / 'stats.json'
            p = subprocess.run([*mode, '--timeout', '10', '--stats-json', str(stats),
                                str(path)], capture_output=True, text=True, timeout=20)
            assert (p.returncode, p.stdout) == (code[expected], expected + '\n'), \
                (mode, p.returncode, p.stdout, p.stderr)
            s = json.loads(stats.read_text())
            assert s['cleanup_complete'] and s['answer'] == expected
            if s.get('engine') == 'batch-group':
                assert s['hedge']['forked'] and s['hedge']['role'] == 'hedge', s
            for r in retained_reports(s):
                if not r or 'error' in r or r.get('engine') != 'retained':
                    continue  # killed by a faster side before it reported
                # A plain check: no preparation stage.
                assert 'prepare' not in r and 'shared_base' not in r, r
                assert r['answer'] == expected, r
            records.append({'fixture': i, 'mode': ' '.join(mode), 'answer': s['answer']})
            clean()
    if group:
        # A theory logic: no hedge is forked; the owner parsed the query once
        # and the group answers alone.
        path = temp / 'abv.smt2'
        path.write_text('(set-logic QF_ABV)(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))'
                        '(declare-const i (_ BitVec 8))(assert (= (select a i) #x01))'
                        '(check-sat)')
        stats = temp / 'stats.json'
        p = subprocess.run([binary, f'-j{min(4, cpus)}', '--timeout', '10', '--stats-json',
                            str(stats), str(path)], capture_output=True, text=True, timeout=20)
        assert (p.returncode, p.stdout) == (10, 'sat\n'), (p.returncode, p.stdout, p.stderr)
        s = json.loads(stats.read_text())
        assert s['engine'] == 'batch-group' and s['winner'] in ('owner', 'root'), s
        assert s['hedge']['forked'] is False and 'QF_ABV' in s['hedge']['reason'], s
        clean()
    if group:
        # One parse per invocation: on a theory logic no hedge parses a
        # second copy, so the summed PSS of the whole process tree at -j4
        # stays within 1.2 times -j1's (sampled every 20 ms).
        big = temp / 'big-abv.smt2'
        with big.open('w') as f:
            f.write('(set-logic QF_ABV)(declare-const a (Array (_ BitVec 32) (_ BitVec 32)))\n')
            # A large parse, decided at once: each read equals itself.
            for i in range(150000):
                read = f'(select a (bvadd v{i} #x{i:08x}))'
                f.write(f'(declare-const v{i} (_ BitVec 32))(assert (= {read} {read}))\n')
            f.write('(check-sat)\n')

        def tree_pss(pid):
            pids, total = [pid], 0
            while pids:
                q = pids.pop()
                try:
                    for line in Path(f'/proc/{q}/smaps_rollup').read_text().splitlines():
                        if line.startswith('Pss:'):
                            total += int(line.split()[1])
                except (FileNotFoundError, ProcessLookupError, PermissionError):
                    continue
                pids += children(q)
            return total

        peaks = {}
        for jobs in ('-j1', f'-j{min(4, cpus)}'):
            p = subprocess.Popen([binary, jobs, '--timeout', '60', str(big)],
                                 stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
            peak = 0
            while p.poll() is None:
                peak = max(peak, tree_pss(p.pid))
                time.sleep(.02)
            out, err = p.communicate()
            assert p.returncode in (0, 10, 20), (jobs, p.returncode, out, err)
            peaks[jobs] = peak
            clean()
        j1, jn = peaks['-j1'], peaks[f'-j{min(4, cpus)}']
        assert jn <= 1.2 * j1, ('one parse per invocation', peaks)
        records.append({'pss_kib': peaks})
print('PASS', json.dumps({'runs': len(records), 'group': group,
                          'pss_kib': records[-1].get('pss_kib') if records else None}))
