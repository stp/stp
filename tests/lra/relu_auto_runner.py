#!/usr/bin/env python3
"""Query-local ReLU selection, exact witnesses, overrides and fallbacks."""
import re
import subprocess
import sys
from relu_runner import source, relu

POLICIES = ('lra-relu-bounds', 'lra-relu-lp', 'lra-model-reconstruction')
OFF = tuple('--' + name + '=off' for name in POLICIES)


def run(solver, text, flags=(), expected=('sat',), ok=True):
    p = subprocess.run([solver, '--SMTLIB2', '-s', '--lra-verify-conflicts=1',
                        *flags], input=text, capture_output=True, text=True,
                       timeout=30)
    if ok:
        assert p.returncode == 0, (flags, p.stdout, p.stderr[-4000:])
        answers = re.findall(r'^(sat|unsat|unknown)$', p.stdout, re.M)
        assert answers == list(expected), (flags, answers, p.stderr[-4000:])
    p.stdout = p.stdout.replace('|', '')  # model printers may quote symbols
    return p


def selections(log):
    return [tuple(map(int, m)) for m in re.findall(
        r'LRA ReLU policy: lp=(\d), automatic_lp=(\d), reconstruction=(\d), '
        r'automatic_reconstruction=(\d)', log)]


def main():
    solver, have_highs = sys.argv[1], sys.argv[2] == 'ON'
    plain = source(['(= x (/ 1 3))', '(= y (+ x (/ 1 6)))'])
    # Explicit compatibility spellings, last-value precedence and parser errors.
    for name in POLICIES:
        for value in ('auto', 'AUTO', 'off', 'OFF', '0', 'false', 'on', 'ON', '1', 'true'):
            supported = have_highs or name != 'lra-relu-lp' or value.lower() not in ('on', '1', 'true')
            p = run(solver, plain, ('--' + name + '=' + value,), ok=supported)
            if not supported:
                assert p.returncode != 0 and 'ENABLE_HIGHS=ON' in p.stderr, p.stderr
        p = run(solver, plain, ('--' + name + '=on', '--' + name + '=off'))
        assert 'LRA ReLU LP:' not in p.stderr
        p = run(solver, plain, ('--' + name + '=banana',), ok=False)
        assert p.returncode != 0 and 'expected auto' in p.stderr, p.stderr

    # AUTO must not turn on affine elimination or reconstruction on ordinary LRA.
    no_presolve = tuple('--lra-presolve-' + s + '=0' for s in
                       ('subst', 'rows', 'bounds', 'propagate', 'unconstrained'))
    chain = source(['(>= x 1)', '(<= x 2)', '(= y (+ x 1))', '(= z (+ y 1))'])
    chain += '(get-value ((- z x)))\n'
    for flags in ((), OFF):
        p = run(solver, chain, flags + no_presolve)
        assert 'LRA ReLU' not in p.stderr and 'LRA reconstruction:' not in p.stderr, p.stderr
        assert re.search(r'\(- z x\) 2\)', p.stdout), p.stdout
    p = run(solver, chain, ('--lra-model-reconstruction=on',) + no_presolve)
    assert 'eliminated=2,' in p.stderr and re.search(r'\(- z x\) 2\)', p.stdout), p.stderr

    graph = ['(>= x (- 1))', '(<= x 1)', '(= a x)', relu('a', 'y'),
             '(= z (+ y (/ 1 3)))']
    query = source(graph + ['(or (> z 1) (< z 0))'])
    query += '(get-value ((- z y)))\n'
    p = run(solver, query)
    assert selections(p.stderr) == ([(1, 1, 1, 1)] if have_highs else [(0, 0, 0, 0)]), p.stderr
    assert re.search(r'\(- z y\) \(/ 1 3\)\)', p.stdout), p.stdout
    if have_highs:
        assert 'witness=1' in p.stderr and 'automatic=1, call_limit=16, budget_seconds=1' in p.stderr, p.stderr
    else:
        assert 'LRA ReLU LP:' not in p.stderr and 'LRA reconstruction:' not in p.stderr, p.stderr

    # Each explicit off overrides automatic selection. All three off restore
    # the original arithmetic pipeline, while later explicit stages imply bounds.
    for flags in (('--lra-relu-lp=off',), ('--lra-model-reconstruction=off',),
                  ('--lra-relu-auto-seconds=0',), ('--lra-relu-lp-seconds=0',),
                  ('--lra-relu-lp-call-seconds=0',)):
        p = run(solver, query, flags)
        assert selections(p.stderr) == [(0, 0, 0, 0)], (flags, p.stderr)
        assert 'LRA ReLU LP:' not in p.stderr and 'LRA reconstruction:' not in p.stderr, p.stderr
    for flags in (('--lra-relu-bounds=off',), OFF):
        p = run(solver, query, flags)
        assert 'LRA ReLU' not in p.stderr and 'LRA reconstruction:' not in p.stderr, p.stderr
    if have_highs:
        p = run(solver, query, ('--lra-relu-bounds=off', '--lra-relu-lp=on',
                                '--lra-relu-auto-seconds=0'))
        assert selections(p.stderr) == [(1, 0, 1, 1)], p.stderr
        assert 'automatic=0, call_limit=2048, budget_seconds=60' in p.stderr, p.stderr
        p = run(solver, query, ('--lra-relu-lp=on', '--lra-model-reconstruction=off'))
        assert selections(p.stderr) == [(1, 0, 0, 0)], p.stderr

    # Named guards require a Boolean model, even when supplied as assumptions.
    header = source(graph).replace('(check-sat)\n', '')
    guarded = header + '(declare-fun p () Bool)\n(assert (=> p (or (> z 1) (< z 0))))\n(check-sat-assuming (p))\n'
    p = run(solver, guarded)
    assert selections(p.stderr) == [(0, 0, 0, 0)] and 'LRA ReLU LP:' not in p.stderr, p.stderr
    impossible_guard = guarded.replace('(or (> z 1) (< z 0))', '(< y 0)')
    p = run(solver, impossible_guard, expected=('unsat',))
    assert selections(p.stderr) == [(0, 0, 0, 0)], p.stderr
    if have_highs:
        p = run(solver, guarded, ('--lra-relu-lp=on', '--lra-model-reconstruction=on'))
        assert selections(p.stderr) == [(1, 0, 1, 0)] and 'witness=1' not in p.stderr, p.stderr

    # Selection cannot stick after an extension or a pop. The third check adds
    # a fresh constraint so the frontend cannot satisfy it from its verdict cache.
    incremental = query.split('(get-value')[0] + '''
(push 1)
(declare-fun p () Bool)
(assert (=> p (< y 0)))
(check-sat-assuming (p))
(pop 1)
(assert (> x (/ 1 2)))
(check-sat)
(get-value ((- z y)))
'''
    p = run(solver, incremental, expected=('sat', 'unsat', 'sat'))
    assert selections(p.stderr) == ([(1, 1, 1, 1), (0, 0, 0, 0), (1, 1, 1, 1)]
                                    if have_highs else [(0, 0, 0, 0)] * 3), p.stderr
    assert re.search(r'\(- z y\) \(/ 1 3\)\)', p.stdout), p.stdout

    # Ineligible topology/input coverage must leave ordinary solving available.
    unbounded = source([relu('x', 'y'), '(or (> y 1) (< y 0))'])
    cycle = source(['(>= x (- 1))', '(<= x 1)', '(= a (+ x 1))',
                    '(= x (- a 1))', relu('x', 'y'), '(>= y 0)'])
    for text in (unbounded, cycle):
        p = run(solver, text)
        assert selections(p.stderr) == [(0, 0, 0, 0)] and 'LRA ReLU LP:' not in p.stderr, p.stderr
    # These cyclic bounds converge towards one without reaching it. AUTO
    # must stop interval work and retain the ordinary substitution path.
    converging = source(['(>= x 0)', '(<= x 1)', '(= a (/ (+ x 1) 2))',
                         '(= x a)', relu('x', 'y'), '(>= y 0)'])
    p = run(solver, converging)
    assert 'bounds_limit=1, lp=0, reconstruction=0' in p.stderr, p.stderr
    run(solver, converging, OFF)
    uf = source(graph + ['(= x (f x))']).replace('(set-logic QF_LRA)',
             '(set-logic QF_UFLRA)\n(declare-fun f (Real) Real)')
    p = run(solver, uf)
    assert selections(p.stderr) == [(0, 0, 0, 0)], p.stderr

    # Zero and strict boundaries retain their exact semantics in every mode.
    for x in (-1, 0, 1):
        value = str(x) if x >= 0 else '(- 1)'
        for flags in ((), OFF):
            for relation, expected in [('=', 'sat'), ('>', 'unsat'), ('<', 'unsat')]:
                text = source([relu('x', 'y'), '(= x ' + value + ')',
                               '(' + relation + ' y ' + str(max(0, x)) + ')'])
                run(solver, text, flags, expected=(expected,))
    # A superficially similar relation with two strict guards excludes x=0.
    malformed = source([relu('x', 'y', strict=True), '(= x 0)'])
    p = run(solver, malformed, expected=('unsat',))
    assert 'LRA ReLU policy:' not in p.stderr, p.stderr

    if have_highs:
        # The triangle admits unequal outputs for duplicate ReLUs, but exact
        # replay never does. Many property objectives exhaust the AUTO call
        # cap, after which ordinary solving must prove the contradiction.
        atoms = ['(or (>= (- y z) (/ 1 ' + str(i) + ')) '
                 '(<= (- y z) (- (/ 1 ' + str(i) + '))))' for i in range(4, 24)]
        text = source(['(>= x (- 1))', '(<= x 1)', relu('x', 'y'), relu('x', 'z'), *atoms])
        p = run(solver, text, expected=('unsat',))
        assert 'rounds=0, calls=16,' in p.stderr and 'witness=1' not in p.stderr, p.stderr
    print('PASS ReLU auto: eligibility, overrides, exact witnesses, budgets, scope and capability')


if __name__ == '__main__':
    main()
