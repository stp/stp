#!/usr/bin/env python3
"""The group against ordinary STP on random formulas, and its exchange.

Random small QF_BV formulas, SAT and UNSAT, products of bit-vectors so that
there is search and therefore clauses to exchange. Each runs ordinarily
(-j1), as plain -jN (the product: root 0 export-only, one clause per own
conflict, the hedge), and through the test driver (stpp-drive), without
the hedge so that the group answers, with an import poll at every conflict:
root 0 importing, budgets of four and 4096, a 16-literal scan window over a
64-literal ring that every root overruns, and sharing off. Every decided
answer must agree with the ordinary one; nothing may stay undecided that
ordinary decided.

Then the exchange itself, on factoring instances that reach a real search:
with every root running to its own answer and root 0 importing too, every
root must import clauses (sat.exchange.imported > 0 in its report), and on
satisfiable instances -- the direction in which a clause that is not implied
would change the answer -- every root must still answer sat.

Arguments: stp-p, stpp-drive, and the number of random formulas.
"""
import ctypes, json, os, random, subprocess, sys, tempfile, time
from pathlib import Path
import sanitizer
binary = str(Path(sys.argv[1]).resolve())
driver = [str(Path(sys.argv[2]).resolve())]
sanitizer.install(binary, driver[0])
count = int(sys.argv[3]) if len(sys.argv) > 3 else 60
assert ctypes.CDLL(None).prctl(36, 1, 0, 0, 0) == 0
os.sched_setaffinity(0, set(sorted(os.sched_getaffinity(0))[:4]))
G = len(os.sched_getaffinity(0))
probe = subprocess.run([binary, '-j2'], input='(set-logic QF_BV)(check-sat)', text=True,
                       capture_output=True, timeout=30)
if G < 3 or (probe.returncode == 2 and 'clause-import' in probe.stderr):
    print(f'SKIP: the group needs three CPUs and clause import ({G} CPUs; {probe.stderr.strip()})')
    sys.exit(0)


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


def formula(rng):
    width = rng.choice([6, 8, 10, 12])
    names = [f'v{i}' for i in range(rng.randint(2, 4))]
    bools = [f'b{i}' for i in range(rng.randint(0, 2))]

    def const():
        return f'(_ bv{rng.randrange(1 << width)} {width})'

    def term(d):
        if d == 0 or rng.random() < 0.3:
            return rng.choice(names) if rng.random() < 0.8 else const()
        op = rng.choice(['bvadd', 'bvmul', 'bvand', 'bvor', 'bvxor', 'bvsub',
                         'bvshl', 'bvlshr', 'bvnot', 'ite', 'bvudiv', 'bvurem'])
        if op == 'bvnot':
            return f'(bvnot {term(d - 1)})'
        if op == 'ite':
            return f'(ite {atom(d - 1)} {term(d - 1)} {term(d - 1)})'
        return f'({op} {term(d - 1)} {term(d - 1)})'

    def atom(d):
        if bools and rng.random() < 0.15:
            b = rng.choice(bools)
            return b if rng.random() < 0.5 else f'(not {b})'
        op = rng.choice(['=', 'bvult', 'bvule', 'bvslt', 'distinct'])
        return f'({op} {term(d)} {term(d)})'

    out = ['(set-logic QF_BV)'] + [f'(declare-const {n} (_ BitVec {width}))' for n in names]
    out += [f'(declare-const {b} Bool)' for b in bools]
    a, b = rng.sample(names, 2)
    out.append(f'(assert (= (bvmul {a} {b}) {const()}))')
    out.append(f'(assert (bvugt {a} (_ bv1 {width})))')
    out.append(f'(assert (bvugt {b} (_ bv1 {width})))')
    for _ in range(rng.randint(1, 4)):
        c = [atom(rng.randint(1, 2)) for _ in range(rng.randint(1, 3))]
        out.append('(assert ' + (c[0] if len(c) == 1 else '(or ' + ' '.join(c) + ')') + ')')
    out.append('(check-sat)')
    return '\n'.join(out) + '\n'


J = f'-j{G}'
alone = [*driver, J, '--hedge', 'none']
modes = {'ordinary': [binary, '-j1'],
         'product': [binary, J],
         'root0-import': [*alone, '--exchange-interval', '1', '--root0-import', 'on'],
         'budget4': [*alone, '--exchange-interval', '1', '--import-budget', '4'],
         'budget4096': [*alone, '--exchange-interval', '1', '--import-budget', '4096'],
         'window': [*alone, '--exchange-interval', '1', '--exchange-ring', '64',
                    '--import-window', '16'],
         'plain': [*alone, '--clause-sharing', 'off']}
code = {'sat': 10, 'unsat': 20, 'unknown': 0}
rng = random.Random(20261004)
tally = {'sat': 0, 'unsat': 0, 'exchanged': 0, 'imported': 0, 'torn': 0}
with tempfile.TemporaryDirectory(prefix='stpp-group-') as temp:
    temp = Path(temp)
    for i in range(count):
        path = temp / f'r{i}.smt2'
        path.write_text(formula(rng))
        answers = {}
        for name, args in modes.items():
            stats = temp / 'stats.json'
            p = subprocess.run([*args, '--timeout', '20', '--stats-json', str(stats),
                                str(path)], capture_output=True, text=True, timeout=40)
            answer = p.stdout.strip()
            assert p.returncode == code.get(answer, -1), (name, i, p.returncode, p.stdout,
                                                          p.stderr, path.read_text())
            answers[name] = answer
            if name != 'ordinary' and answer != 'unknown':
                s = json.loads(stats.read_text())
                assert s['cleanup_complete']
                # The roots that reported before the group stopped.
                for c in s.get('children', []):
                    x = (c.get('report') or {}).get('exchange')
                    if x:
                        tally['exchanged'] += x['exported']
                        tally['imported'] += x['imported']
                        tally['torn'] += x['torn']
            clean()
        ref = answers['ordinary']
        assert ref in ('sat', 'unsat'), (i, answers, path.read_text())
        for name, a in answers.items():
            assert a == ref, (i, name, answers, path.read_text())
        tally[ref] += 1
# Clauses must actually have crossed between roots somewhere in the run.
assert count < 20 or tally['imported'] > 0, tally


def factoring(bits, product):
    half = (bits + 1) // 2
    return ('(set-logic QF_BV)(declare-const x (_ BitVec 40))(declare-const y (_ BitVec 40))'
            f'(assert (= (bvmul x y) (_ bv{product} 40)))(assert (bvugt x (_ bv1 40)))'
            f'(assert (bvugt y (_ bv1 40)))(assert (bvult x (_ bv{1 << half} 40)))'
            f'(assert (bvult y (_ bv{1 << half} 40)))(check-sat)')


# The exchange, on instances that reach a real search (the factoring
# fixtures of tests/api/cpp/before-search.cpp's kind): every root imports.
exchange = {'roots': 0, 'imported': 0}
fixtures = [(factoring(31, 2147483647), 'unsat'), (factoring(33, 8589934583), 'unsat'),
            (factoring(31, 46337 * 46327), 'sat'), (factoring(33, 92681 * 92669), 'sat'),
            (factoring(35, 181243 * 189583), 'sat')]
with tempfile.TemporaryDirectory(prefix='stpp-exchange-') as temp:
    temp = Path(temp)
    for i, (body, expected) in enumerate(fixtures):
        path = temp / f'f{i}.smt2'
        path.write_text(body)
        stats = temp / 'stats.json'
        # Many imports: a poll every 16 conflicts on a sat instance.
        interval = '16' if expected == 'unsat' else '1'
        p = subprocess.run([*driver, J, '--control', 'batch-all', '--root0-import', 'on',
                            '--exchange-interval', interval, '--timeout', '60',
                            '--stats-json', str(stats), str(path)],
                           capture_output=True, text=True, timeout=90)
        assert (p.returncode, p.stdout.strip()) == (code[expected], expected), \
            (i, p.returncode, p.stdout, p.stderr)
        s = json.loads(stats.read_text())
        assert s['forked'] == G and len(s['children']) == G, s
        for c in s['children']:
            assert c['answer'] == expected, (i, c)
            x = c['report']['exchange']
            assert x['backend_imported'] > 0 and x['imported'] > 0, (i, c['slot'], x)
            exchange['roots'] += 1
            exchange['imported'] += x['backend_imported']
        clean()
print('PASS', json.dumps({'formulas': count, **tally, 'exchange': exchange}))
