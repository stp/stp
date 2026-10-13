#!/usr/bin/env python3
"""Compare forked QF_LRA checks with Z3 on deterministic rational problems.

Includes continuous domains, explicit finite domains, strict bounds close to
each other, disequalities, planted rational witnesses and Farkas contradictions.
Retains every input, command, result and per-root report for replay. Run this
separately from timing experiments.
"""
import argparse
from fractions import Fraction as F
import hashlib
import json
import os
from pathlib import Path
import random
import subprocess
import time


def number(value):
    value = F(value)
    numerator = str(value.numerator) if value >= 0 else f'(- {-value.numerator})'
    return numerator if value.denominator == 1 else f'(/ {numerator} {value.denominator})'


def linear(coefficients):
    terms = [f'(* {number(c)} x{i})' for i, c in enumerate(coefficients) if c]
    return '0' if not terms else terms[0] if len(terms) == 1 else '(+ ' + ' '.join(terms) + ')'


def generate(seed, case):
    rng = random.Random((seed << 32) + case)
    count = rng.randrange(3, 8)
    kind = case % 6
    point = [F(rng.randrange(-9, 10), rng.choice((1, 2, 3, 7))) for _ in range(count)]
    epsilon = F(1, rng.choice((7, 1009, 1000000007, 10**18 + 3)))
    constraints = []

    def coefficients():
        out = [F(rng.randrange(-5, 6), rng.choice((1, 1, 2, 3, 7))) for _ in range(count)]
        if not any(out):
            out[0] = F(1)
        return out

    def atom(cs, bound, relation):
        return f'({relation} {linear(cs)} {number(bound)})'

    planted = None
    if kind == 1:
        for i in range(count):
            constraints.append(f'(or (= x{i} {number(point[i])}) '
                               f'(= x{i} {number(point[i] + epsilon)}))')
    if kind == 2:
        for i in range(count):
            constraints += [f'(> x{i} {number(point[i] - epsilon)})',
                            f'(< x{i} {number(point[i] + epsilon)})']
    if kind == 3:
        combined, bound = [F(0)] * count, F(0)
        for _ in range(count + 2):
            cs = coefficients()
            rhs = sum(c * v for c, v in zip(cs, point)) + epsilon
            weight = F(rng.randrange(1, 9), rng.randrange(1, 5))
            constraints.append(atom(cs, rhs, '<='))
            combined = [a + weight * c for a, c in zip(combined, cs)]
            bound += weight * rhs
        constraints.append(atom(combined, bound, '>'))
        planted = 'unsat'
    else:
        for _ in range(rng.randrange(8, 24)):
            atoms = []
            for alternative in range(rng.randrange(1, 4)):
                cs = coefficients()
                at_point = sum(c * v for c, v in zip(cs, point))
                rhs = at_point + rng.choice((-2, -1, 0, 1, 2)) * epsilon
                relation = rng.choice(('<', '<=', '=', 'distinct'))
                if kind == 4 and alternative == 0:
                    rhs = at_point + epsilon
                    relation = '<'
                if kind == 5:
                    # Equivalent hyperplanes expressed at different scales.
                    scale = rng.choice((1, 3, 1000003, F(1, 1000033)))
                    cs, rhs = [scale * c for c in cs], scale * rhs
                atoms.append(atom(cs, rhs, relation))
            constraints.append(atoms[0] if len(atoms) == 1 else '(or ' + ' '.join(atoms) + ')')
        if kind == 4:
            planted = 'sat'
    script = '(set-logic QF_LRA)\n' + ''.join(f'(declare-const x{i} Real)\n' for i in range(count))
    script += ''.join(f'(assert {constraint})\n' for constraint in constraints) + '(check-sat)\n'
    return script, planted


def write_json(path, value):
    path.write_text(json.dumps(value, sort_keys=True, indent=2) + '\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--binary', type=Path, required=True, help='stpp-drive, or stp-p with --public')
    parser.add_argument('--public', action='store_true',
                        help='check public stp-p defaults in the ordinary first-answer race')
    parser.add_argument('--library-dir', type=Path)
    parser.add_argument('--z3', default='z3')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--count', type=int, default=2000)
    parser.add_argument('--seed', type=int, default=20261009)
    parser.add_argument('--jobs', default='1,8,24')
    parser.add_argument('--configs',
                        help='configurations (default: default in public mode; arithmetic variants otherwise)')
    parser.add_argument('--timeout', type=float, default=5)
    parser.add_argument('--worker-mib', type=int, default=4096,
                        help='use 0 for an AddressSanitizer build')
    parser.add_argument('--memory-mib', type=int, default=16384)
    parser.add_argument('--extra', action='append', default=[])
    parser.add_argument('--first-answer', action='store_true',
                        help='exercise the normal race instead of waiting for every root')
    args = parser.parse_args()
    if args.configs is None:
        args.configs = 'default' if args.public else 'default,lra-first-search,lra-lazy,lra-exact'
    jobs = [int(j) for j in args.jobs.split(',')]
    configs = args.configs.split(',')
    if args.public:
        if args.extra or any(c not in ('default', 'eager-arrays') for c in configs):
            parser.error('public mode takes only public configurations and no extra controls')
        args.first_answer = True
    if not jobs or max(jobs) > len(os.sched_getaffinity(0)) or min(jobs) < 1:
        parser.error('job counts must fit the allowed CPUs')
    directory = args.output.resolve()
    directory.mkdir(parents=True, exist_ok=True)
    environment = os.environ.copy()
    if args.library_dir:
        environment['LD_LIBRARY_PATH'] = str(args.library_dir.resolve())
    binary = str(args.binary.resolve())
    configuration = {k: str(v) if isinstance(v, Path) else v for k, v in vars(args).items()}
    configuration['binary_sha256'] = hashlib.sha256(Path(binary).read_bytes()).hexdigest()
    configuration['generator_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    configuration['oracle_version'] = subprocess.run(
        [args.z3, '--version'], capture_output=True, text=True, check=True).stdout.strip()
    if args.library_dir:
        configuration['libraries'] = {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                                      for p in args.library_dir.glob('*.so*')
                                      if p.is_file() and not p.is_symlink()}
    config_path = directory / 'config.json'
    if config_path.exists() and json.loads(config_path.read_text()) != configuration:
        raise SystemExit('output contains a different configuration')
    write_json(config_path, configuration)
    (directory / 'generator.py').write_bytes(Path(__file__).read_bytes())
    log_path = directory / 'results.jsonl'
    done = set()
    if log_path.exists():
        for record in map(json.loads, log_path.read_text().splitlines()):
            if record.get('failures'):
                raise SystemExit('a previous trial failed; retain it and use a new output directory')
            done.add((record['case'], record['jobs']))
    with log_path.open('a', buffering=1) as log:
        for case in range(args.count):
            if all((case, j) in done for j in jobs):
                continue
            script, planted = generate(args.seed, case)
            source = directory / f'{case:06d}.smt2'
            source.write_text(script)
            oracle = subprocess.run([args.z3, '-T:10', str(source)], capture_output=True,
                                    text=True, timeout=15)
            expected = oracle.stdout.strip()
            if expected not in ('sat', 'unsat'):
                raise SystemExit(f'Z3 did not decide {source}: {oracle.stdout} {oracle.stderr}')
            if planted and planted != expected:
                raise SystemExit(f'generator witness/contradiction disagrees with Z3: {source}')
            config = configs[(case // 6) % len(configs)]
            for j in jobs[case % len(jobs):] + jobs[:case % len(jobs)]:
                if (case, j) in done:
                    continue
                stem = directory / f'{case:06d}-j{j}'
                report = stem.with_suffix('.json')
                report.unlink(missing_ok=True)
                command = [binary, f'-j{j}', '--config', config, '--timeout', str(args.timeout),
                           '--stats-json', str(report), '--worker-memory-mib', str(args.worker_mib),
                           '--memory-mib', str(args.memory_mib), *args.extra]
                if j > 1 and not args.public:
                    if not args.first_answer:
                        command += ['--control', 'batch-all']
                    command += ['--exchange-interval', '1', '--exchange-size', '32']
                command.append(str(source))
                started = time.monotonic()
                result = subprocess.run(command, env=environment, capture_output=True,
                                        text=True, timeout=args.timeout + 15)
                answer = result.stdout.strip()
                stem.with_suffix('.stdout').write_text(result.stdout)
                stem.with_suffix('.stderr').write_text(result.stderr)
                record = dict(case=case, jobs=j, config=config, expected=expected, answer=answer,
                              exit_code=result.returncode, command=command,
                              wall_s=time.monotonic() - started)
                failures = []
                if answer not in (expected, 'unknown') or result.returncode != {
                        'sat': 10, 'unsat': 20, 'unknown': 0}.get(answer):
                    failures.append('verdict or exit status disagrees with the oracle')
                if 'Sanitizer' in result.stderr or 'runtime error:' in result.stderr:
                    failures.append('sanitizer diagnostic')
                if report.exists():
                    stats = json.loads(report.read_text())
                    record['children_decided'] = 0
                    record['children_reported'] = 0
                    record['imported'] = 0
                    record['lapped'] = 0
                    record['torn'] = 0
                    if 'error' in stats:
                        failures.append('parallel supervisor reported an error')
                    evidence = stats.get('evidence') or []
                    if isinstance(evidence, dict):
                        evidence = evidence.get('records', [])
                    for event in evidence:
                        if 'failed' in event or 'error' in (event.get('report') or {}):
                            failures.append('failed root in partial supervisor evidence')
                    children = list(stats.get('children', []))
                    hedge = stats.get('hedge')
                    if isinstance(hedge, dict) and hedge.get('forked'):
                        children.append(hedge)
                    for child in children:
                        who = 'hedge' if child.get('role') == 'hedge' else f"root {child.get('slot')}"
                        if child.get('reported', 'unknown') not in (expected, 'unknown'):
                            failures.append(f'{who} disagrees with Z3')
                        status = child.get('wait_status', 0)
                        signal = child.get('signal', 0)
                        if not signal and os.WIFSIGNALED(status):
                            signal = os.WTERMSIG(status)
                        detail = child.get('report') or {}
                        missing_report = (not child.get('killed', False) and
                                          not stats.get('stopped_by') and
                                          os.WIFEXITED(status) and not os.WEXITSTATUS(status) and
                                          detail.get('answer') not in ('sat', 'unsat', 'unknown'))
                        if (missing_report or signal not in (0, 9, 15) or
                                (signal and not child.get('killed', False) and
                                 not stats.get('stopped_by')) or
                                (os.WIFEXITED(status) and os.WEXITSTATUS(status)) or
                                'error' in detail):
                            failures.append(f'{who} failed')
                        record['children_decided'] += child.get('answer') == expected
                        record['children_reported'] += child.get('reported') == expected
                        record['imported'] += detail.get('exchange', {}).get('backend_imported', 0)
                        record['lapped'] += detail.get('exchange', {}).get('lapped', 0)
                        record['torn'] += detail.get('exchange', {}).get('torn', 0)
                else:
                    failures.append('parallel supervisor report is missing')
                record['failures'] = failures
                log.write(json.dumps(record, sort_keys=True) + '\n')
                if failures:
                    raise SystemExit(f'differential failure: {source}, j{j}: {record}')
                print(f'{case:06d} {config} j{j}: {answer} (Z3 {expected})', flush=True)


if __name__ == '__main__':
    main()
