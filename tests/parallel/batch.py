#!/usr/bin/env python3
"""The group's batch side: roots forked at ordinary STP's before-search point.

The controls batch-handoff and batch-all, the policy flags, the transport
settings the checks shrink and the injected faults belong to the test driver
(`stpp-drive`), never to stp-p. Arguments: stp-p and stpp-drive.

1. Hand-off: with no root forked (the test control batch-handoff) the
   owner's own check is published, and it is unknown with the hand-off
   reason -- never a decision -- on SAT and UNSAT inputs that reach search.
2. Fork in the hook: every root of batch-all runs to its own answer, and
   every answer equals the oracle's; the owner's check reports the hand-off.
3. A root killed mid-search does not stop the others from answering, and
   the owner reaps everything.
4. Every mode of the group answers as ordinary STP does.
5. Import budget: every root of batch-all answers the oracle with a
   budget; with root 0 export-only, root 0 exports and never polls or
   imports while the other roots import; with no hedge, every slot is a
   batch root. With root 0 importing, every root imports.
6. Base configuration: --config is the group's base and is recorded in the
   stats. A check that offers no fork point (array reads that survive) is
   searched by the owner itself, once, as -j1 searches it, and the report
   gives the library's reason. So is a check whose roots cannot be forked;
   a root whose setup fails is a failed root.
7. Disagreement: a root that reports a wrong answer while another decides
   ends the invocation with an error and the evidence in the stats -- with
   or without the hedge, never the hedge's answer instead -- and so does a
   root's answer that contradicts the hedge's: the group compares them.
8. --random-seed: root i > 0 searches with the seed plus i.
"""
import ctypes, json, os, random, signal, subprocess, sys, tempfile, time
from pathlib import Path
import sanitizer
binary = str(Path(sys.argv[1]).resolve())
control = [str(Path(sys.argv[2]).resolve())]
sanitizer.install(binary, control[0])
assert ctypes.CDLL(None).prctl(36, 1, 0, 0, 0) == 0
os.sched_setaffinity(0, set(sorted(os.sched_getaffinity(0))[:4]))
if len(os.sched_getaffinity(0)) < 4:
    print('SKIP: these checks need four CPUs')
    sys.exit(0)
probe = subprocess.run([binary, '-j2'], input='(set-logic QF_BV)(check-sat)', text=True,
                       capture_output=True, timeout=30)
if probe.returncode == 2 and 'clause-import' in probe.stderr:
    print('SKIP: this build has no clause import: ' + probe.stderr.strip())
    sys.exit(0)


def children(pid):
    try:
        return [int(x) for x in Path(f'/proc/{pid}/task/{pid}/children').read_text().split()]
    except FileNotFoundError:
        return []


def comm(pid):
    try:
        return Path(f'/proc/{pid}/comm').read_text().strip()
    except (FileNotFoundError, ProcessLookupError):
        return ''


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


def factoring(bits, product):
    half = (bits + 1) // 2
    return ('(set-logic QF_BV)(declare-const x (_ BitVec 40))(declare-const y (_ BitVec 40))'
            f'(assert (= (bvmul x y) (_ bv{product} 40)))(assert (bvugt x (_ bv1 40)))'
            f'(assert (bvugt y (_ bv1 40)))(assert (bvult x (_ bv{1 << half} 40)))'
            f'(assert (bvult y (_ bv{1 << half} 40)))(check-sat)')


code = {'sat': 10, 'unsat': 20, 'unknown': 0}
# Inputs that reach the SAT search (a small product is refuted by the
# simplifier and never reaches the hook): primes, and products of two primes.
fixtures = [(factoring(31, 2147483647), 'unsat'), (factoring(33, 8589934583), 'unsat'),
            (factoring(31, 46337 * 46327), 'sat'), (factoring(33, 92681 * 92669), 'sat')]
records = []
with tempfile.TemporaryDirectory(prefix='stpp-batch-') as temp:
    temp = Path(temp)
    paths = []
    for i, (body, expected) in enumerate(fixtures):
        path = temp / f'{i}.smt2'
        path.write_text(body)
        paths.append((path, expected))
    stats = temp / 'stats.json'

    # 1. The owner's own check, published: unknown with the hand-off reason.
    for path, expected in paths:
        p = subprocess.run([*control, '-j1', '--control', 'batch-handoff', '--timeout', '20',
                            '--stats-json', str(stats), str(path)],
                           capture_output=True, text=True, timeout=40)
        assert (p.returncode, p.stdout) == (0, 'unknown\n'), (path, p.returncode, p.stdout, p.stderr)
        s = json.loads(stats.read_text())
        owner = s['owner_check']
        assert owner['hook_ran'] and owner['answer'] == 'unknown', owner
        assert 'handed to the batch group' in owner['reason'], owner
        assert s['forked'] == 0
        records.append({'handoff': path.name})
        clean()

    # 2. Every root of batch-all answers the oracle's answer.
    for path, expected in paths:
        for sharing in ('on', 'off'):
            p = subprocess.run([*control, '-j3', '--control', 'batch-all', '--clause-sharing',
                                sharing, '--timeout', '30', '--stats-json', str(stats), str(path)],
                               capture_output=True, text=True, timeout=60)
            assert (p.returncode, p.stdout) == (code[expected], expected + '\n'), \
                (path, sharing, p.returncode, p.stdout, p.stderr)
            s = json.loads(stats.read_text())
            assert 'handed to the batch group' in s['owner_check']['reason']
            assert s['forked'] == 3 and len(s['children']) == 3, s
            for c in s['children']:
                assert c['answer'] == expected, c
                assert c['report']['joined']['slot'] == c['slot']
                assert (c['report'].get('exchange') is not None) == (sharing == 'on')
            records.append({'all': path.name, 'sharing': sharing})
            clean()

    # 5. Import budget: every root answers the oracle; root 0 export-only.
    for path, expected in paths:
        for extra in (['--import-budget', '1', '--root0-import', 'on'],
                      ['--import-budget', '4', '--root0-import', 'off']):
            p = subprocess.run([*control, '-j3', '--control', 'batch-all', '--exchange-interval',
                                '16', *extra, '--timeout', '30', '--stats-json', str(stats),
                                str(path)], capture_output=True, text=True, timeout=60)
            assert (p.returncode, p.stdout) == (code[expected], expected + '\n'), \
                (path, extra, p.returncode, p.stdout, p.stderr)
            s = json.loads(stats.read_text())
            assert s['forked'] == 3 and len(s['children']) == 3, s
            importing = extra[-1] == 'on'
            imported = 0
            for c in s['children']:
                assert c['answer'] == expected, c
                r = c['report']
                x = r['exchange']
                assert r['joined']['imports'] == (importing or c['slot'] > 0), r['joined']
                if c['slot'] == 0 and not importing:
                    assert x['polls'] == 0 and x['imported'] == 0 and x['backend_polls'] == 0, x
                    assert x['backend_exported'] > 0 and x['exported'] > 0, x
                else:
                    assert x['polls'] == x['backend_polls'], x
                    imported += x['imported']
            assert imported > 0 or expected == 'sat', s['children']
            records.append({'budget': path.name, 'extra': extra, 'imported': imported})
            clean()
    # No hedge: all three slots are batch roots.
    for path, expected in paths:
        p = subprocess.run([*control, '-j3', '--hedge', 'none', '--timeout', '30',
                            '--stats-json', str(stats), str(path)],
                           capture_output=True, text=True, timeout=60)
        assert (p.returncode, p.stdout) == (code[expected], expected + '\n'), \
            (path, p.returncode, p.stdout, p.stderr)
        s = json.loads(stats.read_text())
        assert s['engine'] == 'batch-group' and s['forked'] == 3 and s['cleanup_complete'], s
        assert s['fork_point'] == 'forked' and s['sharing'], s
        assert all('cpu' not in c['report']['joined'] for c in s['children'] if c['report']), s
        records.append({'no_hedge': path.name})
        clean()
    # With root 0 importing too, every root imports from the others.
    for path, expected in paths[:2]:
        p = subprocess.run([*control, '-j4', '--control', 'batch-all', '--root0-import', 'on',
                            '--exchange-interval', '16', '--timeout', '30', '--stats-json',
                            str(stats), str(path)], capture_output=True, text=True, timeout=60)
        assert (p.returncode, p.stdout) == (code[expected], expected + '\n'), (path, p)
        s = json.loads(stats.read_text())
        for c in s['children']:
            assert c['answer'] == expected, c
            assert c['report']['exchange']['backend_imported'] > 0, c['report']['exchange']
        records.append({'every_root_imports': path.name})
        clean()
    for bad in (['-j1', '--root0-import', 'off'],
                ['-j1', '--import-budget', '1'],
                ['-j3', '--import-budget', '0'],
                ['-j3', '--import-budget', 'none'],
                ['-j3', '--base', 'batch']):
        p = subprocess.run([*control, *bad, str(paths[0][0])], capture_output=True, text=True,
                           timeout=30)
        assert p.returncode == 2 and p.stdout == '', (bad, p.returncode, p.stdout, p.stderr)
        clean()

    # 6. The base configuration.
    for path, expected in paths:
        p = subprocess.run([*control, '-j3', '--hedge', 'none', '--config', 'eager-arrays',
                            '--timeout', '30', '--stats-json', str(stats), str(path)],
                           capture_output=True, text=True, timeout=60)
        assert (p.returncode, p.stdout) == (code[expected], expected + '\n'), (path, p)
        s = json.loads(stats.read_text())
        assert s['base_config'] == 'eager-arrays' and s['forked'] == 3, s
        assert s['fork_point_s'] >= 0 and s['fork_span_s'] >= 0, s
        clean()
        records.append({'base_config': path.name})
    p = subprocess.run([*control, '-j3', '--config', 'retained',
                        str(paths[0][0])], capture_output=True, text=True, timeout=30)
    assert p.returncode == 2 and 'ordinary-route' in p.stderr, p
    clean()
    # No fork point: ten symbolic array reads survive simplification, so the
    # check may refine and the library offers no point. The owner's check
    # searches in place -- one check, encoded once -- as -j1's does, with
    # and without the hedge.
    reads = ''.join(f'(declare-fun i{k} () (_ BitVec 32))' for k in range(10))
    total = '#x00'
    for k in range(10):
        total = f'(bvadd {total} (select a i{k}))'
    for value, expected in (('#x7f', 'sat'),):
        refusing = temp / 'reads.smt2'
        refusing.write_text('(set-logic QF_ABV)(declare-fun a () (Array (_ BitVec 32) (_ BitVec 8)))'
                            + reads + f'(assert (= {total} {value}))(check-sat)')
        alone = subprocess.run([binary, '-j1', '--timeout', '30', str(refusing)],
                               capture_output=True, text=True, timeout=60)
        assert (alone.returncode, alone.stdout) == (code[expected], expected + '\n'), alone
        for args in ([binary, '-j2'], [binary, '-j4'], [*control, '-j3', '--hedge', 'none']):
            p = subprocess.run([*args, '--timeout', '30', '--stats-json', str(stats),
                                str(refusing)], capture_output=True, text=True, timeout=60)
            assert (p.returncode, p.stdout) == (alone.returncode, alone.stdout), (args, p)
            s = json.loads(stats.read_text())
            assert s['engine'] == 'batch-group' and s['fork_point'] == 'refused', s
            assert 'may refine after its first solve' in s['fork_point_reason'], s
            assert 'does not search' not in s['fork_point_reason'], s
            assert s['owner_checks'] == 1 and not s['owner_check']['hook_ran'], s
            clean()
    # An array equality: the same.
    equality = temp / 'equality.smt2'
    equality.write_text('(set-logic QF_ABV)(declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))'
                        '(declare-fun b () (Array (_ BitVec 8) (_ BitVec 8)))'
                        '(assert (= a b))(assert (= (select a #x01) #x02))'
                        '(assert (= (select b #x01) #x03))(check-sat)')
    for args in ([binary, '-j1'], [binary, '-j2'], [binary, '-j4']):
        p = subprocess.run([*args, '--timeout', '30', str(equality)], capture_output=True,
                           text=True, timeout=60)
        assert (p.returncode, p.stdout) == (20, 'unsat\n'), (args, p)
        clean()
    records.append({'refused_fork_point': 2})

    # No root can be forked: the owner's check searches in place, and the
    # report says why, with each fork's errno.
    path, expected = paths[2]  # sat
    p = subprocess.run([*control, '-j3', '--hedge', 'none', '--inject', 'fork-fails',
                        '--timeout', '30', '--stats-json', str(stats), str(path)],
                       capture_output=True, text=True, timeout=60)
    assert (p.returncode, p.stdout) == (code[expected], expected + '\n'), p
    s = json.loads(stats.read_text())
    assert s['fork_point'] == 'failed' and s['owner_checks'] == 1, s
    assert s['fork_errors'] and 'temporarily unavailable' in s['fork_errors'][0]['fork'], s
    clean()
    # With the hedge too: nothing can be forked, and the owner still answers.
    p = subprocess.run([*control, '-j3', '--inject', 'fork-fails', '--timeout', '30',
                        '--stats-json', str(stats), str(path)],
                       capture_output=True, text=True, timeout=60)
    assert (p.returncode, p.stdout) == (code[expected], expected + '\n'), p
    s = json.loads(stats.read_text())
    assert s['fork_point'] == 'failed' and s['winner'] == 'owner', s
    assert not s['hedge']['forked'] and 'temporarily unavailable' in s['hedge']['reason'], s
    clean()
    # A root whose setup fails is a failed root, never an answer: every root
    # failing so is the group's error.
    p = subprocess.run([*control, '-j2', '--hedge', 'none', '--inject', 'fail-root-setup',
                        '--timeout', '30', '--stats-json', str(stats), str(path)],
                       capture_output=True, text=True, timeout=60)
    assert p.returncode == 2 and not p.stdout, p
    assert 'every batch root failed' in p.stderr and 'root setup failed' in p.stderr, p.stderr
    clean()
    records.append({'forks_and_setup': 2})

    # 7. Disagreement: root 1 reports a wrong answer at once and waits.
    path, expected = paths[0]  # unsat
    for args in (['-j3', '--hedge', 'none'], ['-j4', '--control', 'batch-all'],
                 ['-j4', '--inject', 'hold-hedge']):
        inject = ['--inject', 'wrong-root=1:sat']
        if '--inject' in args:  # one --inject holds both faults
            i = args.index('--inject')
            args = args[:i] + args[i + 2:]
            inject = ['--inject', 'wrong-root=1:sat,hold-hedge']
        p = subprocess.run([*control, *args, *inject, '--timeout', '60', '--stats-json',
                            str(stats), str(path)], capture_output=True, text=True, timeout=90)
        assert p.returncode == 2 and p.stdout == '', (args, p.returncode, p.stdout, p.stderr)
        s = json.loads(stats.read_text())
        assert s['fatal'], s
        if 'children' in s['evidence']:
            # The group found it: every process's row.
            assert s['error'] == 'complete answers in the group disagree', s
            reported = {c.get('slot', 'hedge'): c['reported'] for c in s['evidence']['children']}
        else:
            # The supervisor found it first, in the answers the group passed
            # on as they arrived.
            assert s['error'] == 'complete answers disagree', s
            reported = {e.get('root', 'hedge'): e['answer']
                        for e in s['evidence']['records'] if 'answer' in e}
        assert reported[1] == 'sat' and 'unsat' in reported.values(), reported
        records.append({'disagreement': args})
        clean()

    # A root's answer that contradicts the hedge's: root 1 reports sat at once,
    # root 0 waits, and the hedge decides unsat. The group compares the
    # hedge's report with the roots'.
    p = subprocess.run([*control, '-j3', '--inject', 'wrong-root=1:sat,hold-root=0',
                        '--timeout', '60', '--stats-json', str(stats), str(path)],
                       capture_output=True, text=True, timeout=90)
    assert p.returncode == 2 and p.stdout == '', (p.returncode, p.stdout, p.stderr)
    assert 'disagree' in p.stderr, p.stderr
    s = json.loads(stats.read_text())
    assert s['fatal'], s
    rows = s['evidence'].get('children') or []
    records = s['evidence'].get('records') or []
    hedge = [r['reported'] for r in rows if r['role'] == 'hedge'] + \
            [e['answer'] for e in records if e.get('hedge') and 'answer' in e]
    root1 = [r['reported'] for r in rows if r.get('slot') == 1] + \
            [e['answer'] for e in records if e.get('root') == 1 and 'answer' in e]
    assert 'unsat' in hedge and 'sat' in root1, s['evidence']
    records.append({'race_disagreement': True})
    clean()

    # 8. --random-seed: root i > 0 takes the seed plus i.
    path, expected = paths[2]
    p = subprocess.run([*control, '-j3', '--control', 'batch-all', '--random-seed', '7',
                        '--timeout', '30', '--stats-json', str(stats), str(path)],
                       capture_output=True, text=True, timeout=60)
    assert (p.returncode, p.stdout) == (code[expected], expected + '\n'), p
    s = json.loads(stats.read_text())
    seeds = {c['slot']: c['report']['joined'].get('seed') for c in s['children']}
    assert seeds == {0: None, 1: 8, 2: 9}, seeds
    clean()
    # CaDiCaL's seeds are 0..2e9: the reduction wraps root i's seed there.
    p = subprocess.run([*control, '-j3', '--control', 'batch-all', '--random-seed',
                        '1999999999', '--timeout', '30', '--stats-json', str(stats), str(path)],
                       capture_output=True, text=True, timeout=60)
    assert (p.returncode, p.stdout) == (code[expected], expected + '\n'), p
    s = json.loads(stats.read_text())
    seeds = {c['slot']: c['report']['joined'].get('seed') for c in s['children']}
    assert seeds == {0: None, 1: 0, 2: 1}, seeds
    clean()

    # 3. Kill one root mid-search; the others still answer.
    path = temp / 'slow.smt2'
    path.write_text(factoring(35, 34359738337))
    killed = 0
    for attempt in range(3):
        p = subprocess.Popen([binary, '-j4', '--timeout', '60', '--stats-json', str(stats),
                              str(path)],
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        victim = None
        until = time.monotonic() + 20
        while victim is None and time.monotonic() < until and p.poll() is None:
            # supervisor -> owner -> the hedge and three roots
            for owner in children(p.pid):
                roots = [c for c in children(owner) if comm(c) == 'stp-p root']
                if len(roots) == 3:
                    victim = roots[1]
            time.sleep(.005)
        if victim is not None:
            time.sleep(.2)
            try:
                os.kill(victim, signal.SIGKILL)
                killed += 1
            except ProcessLookupError:
                pass
        out, err = p.communicate(timeout=90)
        assert (p.returncode, out) == (20, 'unsat\n'), (p.returncode, out, err)
        s = json.loads(stats.read_text())
        assert s['cleanup_complete']
        clean()
    assert killed > 0, 'never found a running root to kill'
    records.append({'killed_roots': killed})

    # 4. Product modes against ordinary STP on random formulas.
    rng = random.Random(20261005)
    modes = {'ordinary': [binary, '-j1'],
             'product': [binary, '-j4'],
             'no-hedge': [*control, '-j4', '--hedge', 'none'],
             'share': [*control, '-j4', '--exchange-interval', '1', '--import-budget', '4096',
                       '--root0-import', 'on'],
             'plain': [*control, '-j4', '--clause-sharing', 'off'],
             'b1': [*control, '-j4', '--exchange-interval', '1', '--root0-import', 'on'],
             'b4': [*control, '-j4', '--exchange-interval', '1', '--import-budget', '4',
                    '--root0-import', 'on'],
             'b1x': [*control, '-j4', '--exchange-interval', '1']}
    for i in range(24):
        bits = rng.choice([24, 27, 30])
        a, b = rng.randrange(3, 1 << (bits // 2)) | 1, rng.randrange(3, 1 << (bits // 2)) | 1
        product = a * b if rng.random() < 0.5 else a * b + 2
        path = temp / f'r{i}.smt2'
        path.write_text(factoring(bits, product))
        answers = {}
        for name, args in modes.items():
            p = subprocess.run([*args, '--timeout', '30', '--stats-json', str(stats),
                                str(path)], capture_output=True, text=True, timeout=60)
            answers[name] = p.stdout.strip()
            assert p.returncode == code.get(answers[name], -1), (name, p.returncode, p.stdout, p.stderr)
            clean()
        assert answers['ordinary'] in ('sat', 'unsat'), answers
        assert len(set(answers.values())) == 1, (i, answers)
        records.append({'random': i, 'answer': answers['ordinary']})
print('PASS', json.dumps({'runs': len(records), 'killed_roots': killed}))
