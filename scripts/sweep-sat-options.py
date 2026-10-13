#!/usr/bin/env python3
"""Stage a CaDiCaL/Kissat option sweep and confirm finalists on the full corpus."""
import argparse
from collections import Counter, defaultdict
import csv
import fcntl
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time


def write_json(path, value):
    temporary = path.with_suffix(path.suffix + '.tmp')
    temporary.write_text(json.dumps(value, indent=2) + '\n')
    temporary.replace(path)


def write_csv(path, rows):
    temporary = path.with_suffix(path.suffix + '.tmp')
    with temporary.open('w', newline='') as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    temporary.replace(path)


def rank(seed, tag, path):
    return hashlib.sha256(f'{seed}:{tag}:{path}'.encode()).digest()


def samples(manifest, seed, screen_cap=8, refine_cap=24, confirmation_cap=16):
    strata = defaultdict(list)
    for row in manifest:
        size = int(row['bytes'])
        bucket = 0 if size < 100_000 else 1 if size < 1_000_000 else 2 if size < 16_000_000 else 3
        row = dict(row, stratum=f'{row["logic"]}/{row["family"]}/{bucket}')
        strata[row['stratum']].append(row)
    pools = {'training': defaultdict(list), 'confirmation': defaultdict(list)}
    for name, rows in strata.items():
        rows.sort(key=lambda r: rank(seed, 'partition', r['path']))
        nconfirm = max(1, len(rows) // 3) if len(rows) > 1 else 0
        for pool, subset in [('confirmation', rows[:nconfirm]), ('training', rows[nconfirm:])]:
            for row in subset:
                pools[pool][(row['logic'], row['family'])].append(dict(row, population=len(rows), split=pool))

    def choose(pool, cap):
        selected = []
        for family, rows in sorted(pools[pool].items()):
            bins = defaultdict(list)
            for row in rows:
                bins[row['stratum']].append(row)
            queues = {k: iter(sorted(v, key=lambda r: rank(seed, 'within-bin', r['path']))) for k, v in bins.items()}
            chosen = []
            while len(chosen) < cap:
                found = False
                for key in sorted(queues):
                    row = next(queues[key], None)
                    if row is not None:
                        chosen.append(row)
                        found = True
                    if len(chosen) == cap:
                        break
                if not found:
                    break
            selected.extend(chosen)
        return sorted(selected, key=lambda r: rank(seed, 'execution', r['path']))

    return dict(screen=choose('training', screen_cap), refine=choose('training', refine_cap),
                confirmation=choose('confirmation', confirmation_cap))


def config(backend, label, settings=None):
    settings = dict(settings or {})
    args = [f'--{backend}'] + [f'--{name}={value}' for name, value in sorted(settings.items())]
    return dict(name=f'{backend}-{label}', backend=backend, settings=settings, args=args)


def initial_configs():
    modes = [('cadical', 'default', {}), ('cadical', 'sat', {'search-bias': 'sat'}),
             ('cadical', 'unsat', {'search-bias': 'unsat'}),
             ('kissat', 'default', {}), ('kissat', 'sat', {'search-bias': 'sat'}),
             ('kissat', 'focused', {'search-bias': 'unsat'}),
             ('kissat', 'stable', {'kissat-stable': 2}),
             ('kissat', 'stable-sat', {'kissat-stable': 2, 'search-bias': 'sat'})]
    result = []
    for backend, label, settings in modes:
        result.append(config(backend, label, settings))
        result.append(config(backend, label + '-phase0', dict(settings, **{'sat-phase': 0})))
    for backend in ('cadical', 'kissat'):
        for phase in (0, 1):
            result.append(config(backend, f'forced-{phase}', {'sat-phase': phase, 'sat-forcephase': 1}))
        for bias in ('none', 'sat'):
            settings = {} if bias == 'none' else {'search-bias': bias}
            result.append(config(backend, f'{bias}-no-rephase', dict(settings, **{'sat-rephase': 0})))
            result.append(config(backend, f'{bias}-no-target', dict(settings, **{'sat-target': 0})))
        result.append(config(backend, 'target-focused', {'sat-target': 2}))
    result.append(config('cadical', 'stable-rephase', {'sat-rephase': 2}))
    result.append(config('kissat', 'stable-sat-no-rephase',
                         {'kissat-stable': 2, 'search-bias': 'sat', 'sat-rephase': 0}))
    return result


def deduplicate(configurations):
    result, seen = [], set()
    for item in configurations:
        key = tuple(item['args'])
        if key not in seen:
            result.append(item)
            seen.add(key)
    return result


def analyze(directory, configs, manifest, runner):
    observations = runner.read_journals(directory)
    if len(observations) != len(configs) * len(manifest):
        raise RuntimeError(f'incomplete stage: {directory}')
    summary = json.loads((directory / 'summary.json').read_text())
    if not summary['valid']:
        raise RuntimeError(f'answer audit failed: {directory}')
    counts = Counter(row.get('stratum', row['logic'] + '/' + row['family']) for row in manifest)
    populations = {row.get('stratum', row['logic'] + '/' + row['family']): int(row.get('population', counts[row.get('stratum', row['logic'] + '/' + row['family'])])) for row in manifest}
    lookup = {row['path']: row for row in manifest}
    own = defaultdict(list)
    for row in observations:
        own[row['solver']].append(row)
    rankings = []
    for candidate in configs:
        rows = own[candidate['name']]
        total = 0.0
        for observation in rows:
            source = lookup[observation['path']]
            key = source.get('stratum', source['logic'] + '/' + source['family'])
            total += observation['par2'] * populations[key] / counts[key]
        rankings.append(dict(name=candidate['name'], backend=candidate['backend'],
                             weighted_par2=total / sum(populations.values()),
                             par2_mean=sum(row['par2'] for row in rows) / len(rows),
                             solved=sum(row['status'] == 'solved' for row in rows), n=len(rows)))
    rankings.sort(key=lambda row: (row['weighted_par2'], row['name']))
    result = dict(rankings=rankings, population_represented=sum(populations.values()),
                  sample_files=len(manifest), disagreements=0)
    write_json(directory / 'ranking.json', result)
    write_csv(directory / 'ranking.csv', rankings)
    return rankings


def winner(configs, ranking, backend, exclude_default=False):
    by_name = {c['name']: c for c in configs}
    return next(by_name[row['name']] for row in ranking if row['backend'] == backend and
                (not exclude_default or row['name'] != f'{backend}-default'))


def refine_configs(screen_configs, ranking):
    result = [config(backend, 'default') for backend in ('cadical', 'kissat')]
    for backend in ('cadical', 'kissat'):
        leaders = [winner(screen_configs, ranking, backend),
                   winner(screen_configs, ranking, backend, True)]
        for number, leader in enumerate(leaders):
            for encoder in ('auto', 'new-medium', 'gia-low'):
                for factor in ('on', 'off'):
                    settings = dict(leader['settings'])
                    if encoder != 'auto':
                        settings['cnf-generation-effort'] = encoder
                    if factor != 'on':
                        settings['cadical-factor'] = factor
                    result.append(config(backend, f'refine-{number}-{encoder}-{factor}', settings))
            settings = dict(leader['settings'])
            if backend == 'cadical':
                settings['cadical-elim'] = 0
            else:
                settings['refinement-trail-reuse'] = 'false'
                settings['kissat-trail-reuse'] = 'false'
            result.append(config(backend, f'refine-{number}-no-elim-or-reuse', settings))
    return deduplicate(result)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--campaign', required=True, type=Path)
    parser.add_argument('--root', type=Path)
    parser.add_argument('--manifest', type=Path)
    parser.add_argument('--binary', type=Path)
    parser.add_argument('--framework', type=Path)
    parser.add_argument('--runner-checkout', type=Path)
    parser.add_argument('--seed', type=int, default=202610131729)
    parser.add_argument('--logic', default='QF_BV', help='logic to sweep; defaults to QF_BV')
    parser.add_argument('--timeout', type=float, default=24)
    parser.add_argument('--memory-gb', type=float, default=8)
    parser.add_argument('--workers', type=int, default=24)
    parser.add_argument('--screen-per-family', type=int, default=8)
    parser.add_argument('--refine-per-family', type=int, default=24)
    parser.add_argument('--confirmation-per-family', type=int, default=16)
    parser.add_argument('--status', action='store_true')
    args = parser.parse_args()
    campaign = args.campaign.resolve()
    if args.status:
        state = json.loads((campaign / 'state.json').read_text())
        try:
            os.kill(state['pid'], 0)
            state['controller_alive'] = True
        except ProcessLookupError:
            state['controller_alive'] = False
        if state.get('active_output'):
            target = Path(state['active_output'])
            counts = Counter()
            for journal in target.glob('cpu-*.jsonl'):
                for line in journal.open():
                    if line.endswith('\n'):
                        observation = json.loads(line)
                        counts[observation['status']] += 1
            state['observed'] = sum(counts.values())
            state['outcomes'] = dict(counts)
            if (target / 'metadata.json').exists():
                meta = json.loads((target / 'metadata.json').read_text())
                state['expected'] = meta['files'] * len(meta['configurations'])
        print(json.dumps(state, indent=2))
        return
    for name in ('root', 'manifest', 'binary', 'framework', 'runner_checkout'):
        if getattr(args, name) is None:
            parser.error(f'--{name.replace("_", "-")} is required')
    if (args.screen_per_family < 1 or args.refine_per_family < args.screen_per_family
            or args.confirmation_per_family < 1):
        parser.error('sample caps must be positive and refinement must include the screening sample')
    campaign.mkdir(parents=True, exist_ok=True)
    with (campaign / 'controller.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        try:
            orchestrate(args, campaign)
        except Exception as error:
            state_path = campaign / 'state.json'
            state = json.loads(state_path.read_text()) if state_path.exists() else {}
            state.update(state='failed', error=str(error),
                         ended=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()))
            write_json(state_path, state)
            raise


def orchestrate(args, campaign):
    runner_path = args.runner_checkout / 'scripts/benchmark-sat-backends.py'
    spec = importlib.util.spec_from_file_location('sweep_runner', runner_path)
    runner = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(runner)
    manifest = [row for row in csv.DictReader(args.manifest.open()) if row['logic'] == args.logic]
    if not manifest:
        raise ValueError(f'no inputs for {args.logic}')
    if len(manifest) != len({row['path'] for row in manifest}):
        raise ValueError('full manifest contains duplicate files')
    selected = samples(manifest, args.seed, args.screen_per_family,
                       args.refine_per_family, args.confirmation_per_family)
    selection = campaign / 'selection'
    plan = dict(seed=args.seed, logic=args.logic, files=len(manifest), stages={k:len(v) for k,v in selected.items()},
                per_family=dict(screen=args.screen_per_family, refine=args.refine_per_family,
                                confirmation=args.confirmation_per_family),
                timeout=args.timeout, memory_gb=args.memory_gb, workers=args.workers,
                solvers=['cadical', 'kissat'], sampling='family and file-size strata; training/confirmation partitioned before candidate results',
                root=str(args.root.resolve()), manifest_sha256=runner.sha256_file(args.manifest),
                controller_sha256=runner.sha256_file(Path(__file__)),
                framework_sha256=runner.sha256_file(args.framework),
                runner_sha256=runner.sha256_file(runner_path), binary_sha256=runner.sha256_file(args.binary))
    if (campaign / 'plan.json').exists() and json.loads((campaign / 'plan.json').read_text()) != plan:
        raise ValueError('campaign parameters or archived components changed')
    write_json(campaign / 'plan.json', plan)
    selection.mkdir(exist_ok=True)
    for label, rows in selected.items():
        write_csv(selection / (label + '.csv'), rows)
    write_csv(selection / 'all.csv', manifest)
    state = dict(state='running', pid=os.getpid(), started=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()))
    current, stopped = None, False

    def halt(signum, frame):
        nonlocal stopped
        stopped = True
        if current is not None and current.poll() is None:
            current.send_signal(signal.SIGTERM)

    for signum in (signal.SIGTERM, signal.SIGINT):
        signal.signal(signum, halt)
    environment = os.environ.copy()
    environment['LD_LIBRARY_PATH'] = str(args.binary.parent.parent / 'lib') + ':' + environment.get('LD_LIBRARY_PATH','')

    def stage(label, configurations, rows):
        nonlocal current
        if stopped:
            raise SystemExit('sweep stopped')
        profiles = campaign / (label + '-profiles.json')
        if profiles.exists() and json.loads(profiles.read_text()) != configurations:
            raise ValueError(f'candidate selection changed on resume: {label}')
        write_json(profiles, configurations)
        stage_manifest = selection / (label + '.csv')
        write_csv(stage_manifest, rows)
        output = campaign / label
        state.update(stage=label, active_output=str(output), configurations=len(configurations), files=len(rows))
        write_json(campaign / 'state.json', state)
        finished = (output / 'state.json').exists() and json.loads((output / 'state.json').read_text())['state'] == 'complete'
        if not finished:
            command = [sys.executable, str(args.framework), '--stp-checkout', str(args.runner_checkout),
                       'run', '--root', str(args.root), '--manifest', str(stage_manifest), '--binary', str(args.binary),
                       '--configs', str(profiles), '--output', str(output), '--timeout', str(args.timeout),
                       '--memory-gb', str(args.memory_gb), '--workers', str(args.workers)]
            if (output / 'metadata.json').exists():
                command.append('--resume')
            print(f'Starting {label}: {len(rows)} files x {len(configurations)} configurations', flush=True)
            with (campaign / (label + '.log')).open('a') as log:
                current = subprocess.Popen(command, stdout=log, stderr=subprocess.STDOUT,
                                           stdin=subprocess.DEVNULL, env=environment, start_new_session=True)
                state['active_pid'] = current.pid
                write_json(campaign / 'state.json', state)
                returncode = current.wait()
                current = None
            if stopped:
                state['state'] = 'stopped'
                write_json(campaign / 'state.json', state)
                raise SystemExit('sweep stopped; recorded observations preserved')
            if returncode:
                state['state'] = 'failed'
                write_json(campaign / 'state.json', state)
                raise SystemExit(f'{label} failed ({returncode}); inspect its log')
        ranking = analyze(output, configurations, rows, runner)
        print(json.dumps(dict(stage=label,leaders=ranking[:4])),flush=True)
        return ranking

    screen_configs = initial_configs()
    screen_ranking = stage('screen', screen_configs, selected['screen'])
    refined = refine_configs(screen_configs, screen_ranking)
    refined_ranking = stage('refine', refined, selected['refine'])
    finalists = [config(backend, 'default') for backend in ('cadical','kissat')]
    for backend in ('cadical','kissat'):
        best = winner(refined,refined_ranking,backend,True)
        finalists.append(config(backend,'tuned',best['settings']))
    write_json(campaign / 'finalists.json', finalists)
    seeds = []
    for finalist in finalists:
        for seed in (0,1,2):
            settings = dict(finalist['settings'])
            if seed:
                settings['random-seed'] = seed
            seeds.append(config(finalist['backend'], finalist['name'].split('-',1)[1]+f'-seed{seed}',settings))
    stage('confirmation', seeds, selected['confirmation'])
    stage('all-corpus',finalists,manifest)
    final = json.loads((campaign / 'all-corpus/summary.json').read_text())
    write_json(campaign / 'final-summary.json', final)
    state.update(state='complete',ended=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()))
    write_json(campaign / 'state.json',state)
    print('Sweep and full-corpus confirmation complete.',flush=True)


if __name__ == '__main__':
    main()
