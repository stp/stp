#!/usr/bin/env python3
"""The test driver's configuration table, --config and --portfolio races.

The table, the portfolios and --pin are the test driver's (stpp-drive);
stp-p offers --config default and eager-arrays only. Arguments: stp-p,
stpp-drive."""
import ctypes, json, os
from pathlib import Path
import signal, subprocess, sys, tempfile, time
import sanitizer
binary = str(Path(sys.argv[1]).resolve())
driver = [str(Path(sys.argv[2]).resolve())]
sanitizer.install(binary, driver[0])
assert ctypes.CDLL(None).prctl(36, 1, 0, 0, 0) == 0
os.sched_setaffinity(0, set(sorted(os.sched_getaffinity(0))[:4]))
cpus = sorted(os.sched_getaffinity(0)); assert len(cpus) >= 2, cpus

def children(pid):
    try: return [int(x) for x in Path(f'/proc/{pid}/task/{pid}/children').read_text().split()]
    except FileNotFoundError: return []
def clean():
    until = time.monotonic() + 5
    while time.monotonic() < until:
        while True:
            try: pid, _ = os.waitpid(-1, os.WNOHANG)
            except ChildProcessError: break
            if not pid: break
        if not children(os.getpid()): return
        time.sleep(.002)
    raise AssertionError(('owned processes remain', children(os.getpid())))

table = subprocess.run([*driver, '--list-configs'], capture_output=True, text=True, check=True)
names = [line.split('\t')[0] for line in table.stdout.splitlines()]
assert names[:2] == ['default', 'eager-arrays'] and 'retained' in names, names
assert 'fp-abstraction' not in names and len(set(names)) == len(names), names
assert subprocess.run([binary, '--list-configs'], capture_output=True).returncode == 2
records = {'configs': len(names), 'cases': []}
fixtures = [('(assert true)', 'sat'), ('(assert false)', 'unsat'),
            ('(declare-const x (_ BitVec 8))(declare-const y (_ BitVec 8))'
             '(assert (= (bvmul x y) #x0f))(assert (bvugt x #x01))', 'sat'),
            ('(declare-const x (_ BitVec 8))(assert (bvult x #xff))'
             '(assert (= (bvadd x #x01) #x00))', 'unsat')]
with tempfile.TemporaryDirectory(prefix='stpp-portfolio-') as temp:
    temp = Path(temp)
    paths = []
    for i, (body, expected) in enumerate(fixtures):
        path = temp / f'{i}.smt2'; path.write_text('(set-logic QF_BV)' + body + '(check-sat)')
        paths.append((path, expected))
    code = {'sat': 10, 'unsat': 20}
    # Every configuration decides every fixture on the -j1 route, but for one
    # whose options name a backend this build lacks (no-factor without
    # CaDiCaL), which is refused as such.
    unavailable = set()
    for name in names:
        for path, expected in paths:
            stats = temp / 'stats.json'
            p = subprocess.run([*driver, '-j1', '--config', name, '--timeout', '5', '--stats-json',
                                str(stats), str(path)], capture_output=True, text=True, timeout=10)
            if p.returncode == 2 and 'needs a build with' in p.stderr:
                unavailable.add(name)
                break
            assert (p.returncode, p.stdout) == (code[expected], expected + '\n'), (name, p.stdout, p.stderr)
            assert json.loads(stats.read_text())['config'] == name
    # Portfolios: one single-CPU side per configuration. Placement is the
    # scheduler's; with --pin the sides take the last allowed CPUs first.
    for jobs, portfolio in [(2, 'default,seed1'), (3, 'default,retained,no-factor'),
                            (4, 'default,cnf-gia-high,no-factor,cnf-new-low')]:
        if jobs > len(cpus) or unavailable & set(portfolio.split(',')):
            continue
        sides = portfolio.split(',')
        for pin in ([], ['--pin']):
            for path, expected in paths:
                stats = temp / 'stats.json'
                p = subprocess.run([*driver, f'-j{jobs}', '--portfolio', portfolio, *pin,
                                    '--timeout', '5', '--stats-json', str(stats), str(path)],
                                   capture_output=True, text=True, timeout=10)
                assert (p.returncode, p.stdout) == (code[expected], expected + '\n'), (portfolio, p.stdout, p.stderr)
                s = json.loads(stats.read_text())
                assert s['cleanup_complete'] and s['portfolio'] == sides
                assert sum(x['slots'] for x in s['sides']) == jobs
                assert len(s['sides']) == len(sides)
                assert s['retained_slots'] == sides.count('retained')
                assert [x['config'] for x in s['sides'][:len(sides)]] == sides
                assert [x['cpu'] for x in s['sides'][:len(sides)]] == \
                    ([cpus[jobs - 1 - i] for i in range(len(sides))] if pin else [-1] * len(sides))
                winner = next(x for x in s['sides'] if x['role'] == s['winner'] and
                              x['config'] == s['winner_config'])
                assert winner['completed_report'] and (winner['wait_code'], winner['wait_value']) == (1, 0)
                for x in s['sides']:
                    if x is not winner and x['cancelled']:
                        assert x['cancellation_sent']
                records['cases'].append({'jobs': jobs, 'portfolio': portfolio, 'pin': bool(pin),
                                         'winner': s['winner_config'] or s['winner']})
                clean()
    # Killing one configuration leaves the other able to answer; killing all
    # of them is an error, as the death of -j1's process is.
    path = temp / 'slow-parse-sat.smt2'
    path.write_text('(set-logic QF_BV)(declare-const x (_ BitVec 32))' +
                    '(assert (= (bvadd x (_ bv0 32)) x))' * 35000 + '(check-sat)')
    for kill in [[0], [1], [0, 1]]:
        p = subprocess.Popen([*driver, '-j2', '--portfolio', 'default,seed1', '--timeout', '6', str(path)],
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        until = time.monotonic() + 3; sides = []
        while time.monotonic() < until:
            owners = children(p.pid)
            if owners and len(children(owners[0])) == 2:
                sides = children(owners[0]); break
            time.sleep(.0005)
        assert sides, 'portfolio sides not observed'
        for i in kill: os.kill(sides[i], signal.SIGKILL)
        out, err = p.communicate(timeout=10)
        if len(kill) == 2:
            assert p.returncode == 2 and not out and 'every side failed' in err, (kill, p.returncode, out, err)
        else:
            assert (p.returncode, out) == (10, 'sat\n'), (kill, p.returncode, out, err)
        clean(); records['cases'].append({'killed': kill, 'answer': out.strip() or 'error'})
    # No side can be forked: the race runs the first side's route itself.
    stats = temp / 'stats.json'
    p = subprocess.run([*driver, '-j2', '--portfolio', 'default,seed1', '--inject', 'fork-fails',
                        '--timeout', '5', '--stats-json', str(stats), str(paths[0][0])],
                       capture_output=True, text=True, timeout=10)
    assert (p.returncode, p.stdout) == (10, 'sat\n'), p
    s = json.loads(stats.read_text())
    assert s['engine'] == 'ordinary' and len(s['race_fork_errors']) == 2, s
    clean(); records['cases'].append({'no_side_forked': True})
    # A portfolio and the retained route take QF_BV only.
    theory = temp / 'theory.smt2'
    theory.write_text('(set-logic QF_ABV)(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))'
                      '(assert (= (select a #x00) #x01))(check-sat)')
    for strict in (['-j2', '--portfolio', 'default,seed1'], ['-j1', '--config', 'retained']):
        p = subprocess.run([*driver, *strict, str(theory)], capture_output=True, text=True,
                           timeout=10)
        assert p.returncode == 2 and not p.stdout and 'QF_BV' in p.stderr, (strict, p)
    for args in [['-j2', '--portfolio', 'nonesuch'], ['-j2', '--portfolio', 'default,default'],
                 ['-j2', '--portfolio', 'default,seed1,seed2'], ['-j1', '--portfolio', 'default'],
                 ['-j2', '--portfolio', 'default'], ['-j3', '--portfolio', 'default,seed1'],
                 ['-j2', '--portfolio', 'default,seed1', '--config', 'seed2'],
                 ['-j2', '--portfolio', 'default,seed1', '--hedge', 'none'],
                 ['-j2', '--portfolio', 'default,seed1', '--ordinary-root', 'on'],
                 ['--config', 'nonesuch'], ['--config', 'no-simplify'],
                 ['--config', 'fp-abstraction']]:
        p = subprocess.run([*driver, *args, str(paths[0][0])], capture_output=True, text=True, timeout=5)
        assert p.returncode == 2 and not p.stdout, (args, p.returncode, p.stdout)
print(json.dumps({'pass': True, **records}, indent=2))
