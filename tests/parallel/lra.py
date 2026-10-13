"""LRA forked checks, theory refinement and shared clauses under assumptions.

The random oracle enumerates explicit two-point Real domains using rational
arithmetic. It does not use STP or assume that unconstrained Reals are integers.
"""
import itertools
import json
import os
from pathlib import Path
import random
import subprocess
import sys
import tempfile
from fractions import Fraction

import sanitizer


binary, driver = (str(Path(arg).resolve()) for arg in sys.argv[1:3])
sanitizer.install(binary, driver)
available_cpus = sorted(os.sched_getaffinity(0))
cpus = available_cpus[:4]
os.sched_setaffinity(0, set(cpus))
jobs = min(3, len(cpus))
probe = subprocess.run([binary, f'-j{jobs}'], input='(set-logic QF_LRA)(check-sat)',
                       text=True, capture_output=True, timeout=30)
parallel = jobs > 1 and not (probe.returncode == 2 and 'clause-import' in probe.stderr)
codes = {'sat': 10, 'unsat': 20, 'unknown': 0}


def choices(count, satisfiable):
    terms = [f'r{i}' for i in range(count)]
    declarations = ''.join(f'(declare-const {term} Real)' for term in terms)
    domains = ''.join(f'(assert (or (= {term} 0) (= {term} 1)))' for term in terms)
    numerator = 2 * (count // 2) + int(not satisfiable)
    return ('(set-logic QF_LRA)' + declarations + domains +
            f'(assert (= (+ {" ".join(terms)}) (/ {numerator} 2)))(check-sat)')


def rational(value):
    value = Fraction(value)
    n = str(value.numerator) if value >= 0 else f'(- {-value.numerator})'
    return n if value.denominator == 1 else f'(/ {n} {value.denominator})'


with tempfile.TemporaryDirectory(prefix='stpp-lra-') as temporary:
    directory = Path(temporary)
    source, report = directory / 'query.smt2', directory / 'stats.json'

    def run(body, answer, options=(), executable=binary):
        source.write_text(body)
        report.unlink(missing_ok=True)
        result = subprocess.run([executable, *options, '--timeout', '20',
                                 '--stats-json', str(report), str(source)],
                                text=True, capture_output=True, timeout=35)
        assert (result.returncode, result.stdout) == (codes[answer], answer + '\n'), (
            options, body, result.returncode, result.stdout, result.stderr)
        stats = json.loads(report.read_text())
        assert stats['answer'] == answer, stats
        return stats

    # Admission, exact strict bounds, non-binary rational witnesses, and
    # negative equality. These may be decided before the fork point.
    fixtures = [
        ('(declare-const x Real)(assert (> x (/ 1 3)))(assert (< x (/ 2 3)))', 'sat'),
        ('(declare-const x Real)(assert (> x (/ 1 3)))(assert (<= x (/ 1 3)))', 'unsat'),
        ('(declare-const x Real)(assert (= (* 3 x) 1))(assert (not (= x 0)))', 'sat'),
        ('(declare-const x Real)(declare-const y Real)'
         '(assert (or (< x y) (> x y)))(assert (<= x y))(assert (>= x y))', 'unsat'),
    ]
    for body, answer in fixtures:
        for count in ([1, jobs] if parallel else [1]):
            run('(set-logic QF_LRA)' + body + '(check-sat)', answer, [f'-j{count}'])

    if parallel:
        # Exercise the public group at small and larger worker counts.
        os.sched_setaffinity(0, set(available_cpus))
        try:
            for count in (8, 9, 24):
                if count > len(available_cpus):
                    continue
                stats = run(choices(4, False), 'unsat', [f'-j{count}'])
                assert stats['fork_point'] == 'forked' and stats['forked'] == count, stats
        finally:
            os.sched_setaffinity(0, set(cpus))

        imported = 0
        for config in ('default', 'lra-first-search', 'lra-lazy', 'lra-exact'):
            for satisfiable in (False, True):
                answer = 'sat' if satisfiable else 'unsat'
                body = choices(8, satisfiable)
                for sharing in ('on', 'off'):
                    stats = run(body, answer, [f'-j{jobs}', '--control', 'batch-all',
                                               '--config', config, '--clause-sharing', sharing,
                                               '--exchange-interval', '1', '--exchange-size', '32'],
                                driver)
                    assert stats['fork_point'] == 'forked', stats
                    assert stats['forked'] == jobs, stats
                    assert stats['owner_check']['answer'] == 'unknown', stats
                    assert len(stats['children']) == jobs, stats
                    for child in stats['children']:
                        assert child['answer'] == answer, child
                        assert child['report']['joined']['rediversifications'] == 0, child
                        if child['slot']:
                            joined = child['report']['joined']
                            assert joined['diversified'], joined
                        if sharing == 'on':
                            exchange = child['report']['exchange']
                            imported += exchange['backend_imported']
                            if child['slot'] == 0:
                                assert exchange['backend_imported'] == 0, exchange
                # Public first-answer path, including termination/reaping of
                # the other roots, uses exactly the same arithmetic fork.
                stats = run(body, answer, [f'-j{jobs}'])
                assert stats['fork_point'] == 'forked', stats
                assert stats['winner'] == 'root', stats
                assert not stats['hedge']['forked'], stats
        assert imported > 0, 'no arithmetic clause was imported in the sharing checks'

        if jobs >= 3:
            # A complete answer from a process that is still alive cannot
            # stop forking. Root 0 is held; root 1 writes a false SAT answer
            # and waits; root 2 must start and expose the contradiction.
            source.write_text(choices(4, False))
            result = subprocess.run(
                [driver, '-j3', '--timeout', '3',
                 '--inject', 'hold-root=0,wrong-root=1:sat',
                 '--stats-json', str(report), str(source)],
                text=True, capture_output=True, timeout=15)
            assert result.returncode == 2 and not result.stdout, result
            assert ('complete answers' in result.stderr and
                    'disagree' in result.stderr), result.stderr

        stats = run(choices(6, False), 'unknown',
                    ['-j1', '--control', 'batch-handoff'], driver)
        assert stats['owner_check']['hook_ran'], stats
        assert 'handed to the batch group' in stats['owner_check']['reason'], stats
        assert stats['forked'] == 0, stats
        # A failed fork leaves the whole check in the owner, with arithmetic
        # still connected, rather than publishing the Boolean skeleton.
        stats = run(choices(6, False), 'unsat',
                    [f'-j{jobs}', '--inject', 'fork-fails'], driver)
        assert stats['winner'] == 'owner' and stats['forked'] == 0, stats

        # A full arithmetic reroute constructs a private new encoding. It
        # must drop the old exchange and must not offer a second fork point.
        reroute = Path(__file__).resolve().parents[1] / 'query-files' / 'lra-float-reroute-preserves-answer.smt2'
        stats = run(reroute.read_text(), 'sat',
                    [f'-j{jobs}', '--control', 'batch-all', '--config', 'lra-reroute',
                     '--exchange-interval', '1'], driver)
        assert stats['forked'] == jobs, stats
        for child in stats['children']:
            assert child['answer'] == 'sat', child

    rng = random.Random(74119)
    for case in range(24):
        count = 5
        clauses = []
        for _ in range(rng.randrange(3, 8)):
            atoms = []
            for _ in range(rng.randrange(1, 4)):
                coefficients = [rng.randrange(-3, 4) for _ in range(count)]
                rhs = Fraction(rng.randrange(-10, 11), rng.randrange(1, 5))
                relation = rng.choice(('<', '<=', '='))
                atoms.append((coefficients, rhs, relation))
            clauses.append(atoms)

        def holds(values, atom):
            coefficients, rhs, relation = atom
            lhs = sum(c * v for c, v in zip(coefficients, values))
            return lhs < rhs if relation == '<' else lhs <= rhs if relation == '<=' else lhs == rhs

        satisfiable = any(all(any(holds(values, atom) for atom in clause) for clause in clauses)
                          for values in itertools.product((0, 1), repeat=count))
        body = '(set-logic QF_LRA)' + ''.join(
            f'(declare-const r{i} Real)(assert (or (= r{i} 0) (= r{i} 1)))' for i in range(count))
        for clause in clauses:
            atoms = []
            for coefficients, rhs, relation in clause:
                lhs = '(+ ' + ' '.join(f'(* {rational(c)} r{i})'
                                      for i, c in enumerate(coefficients)) + ')'
                atoms.append(f'({relation} {lhs} {rational(rhs)})')
            clause_text = atoms[0] if len(atoms) == 1 else '(or ' + ' '.join(atoms) + ')'
            body += '(assert ' + clause_text + ')'
        body += '(check-sat)'
        for count_jobs in ([1, jobs] if parallel else [1]):
            options = [f'-j{count_jobs}']
            if count_jobs > 1:
                options += ['--exchange-interval', '1', '--control', 'batch-all']
            run(body, 'sat' if satisfiable else 'unsat', options,
                driver if count_jobs > 1 else binary)

print('LRA arithmetic refinement, shared clauses, strict bounds and rational oracle passed')
