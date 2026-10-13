#!/usr/bin/env python3
"""Select real SMT-LIB sessions and compare complete-session PAR2.

Use select --all for a complete corpus, or the sampled selection for tuning.
Run each configuration on the same files, pinned to a CPU, in rotating order.
Every check-sat must return a definite answer; incomplete sessions, UNKNOWN,
errors, wrong answers, and timeouts receive twice the session time limit.
Runs preserve per-observation journals and can be continued with --resume.
"""
import argparse
from collections import defaultdict
import concurrent.futures
import csv
import fcntl
import hashlib
import itertools
import json
import os
from pathlib import Path
import platform
import re
import signal
import shutil
import subprocess
import threading
import time

CHECK = re.compile(rb'\(\s*check-sat(?:-assuming)?\b')
NON_COMMAND = re.compile(rb'"(?:[^"]|"")*"|\|[^|]*\||;[^\n]*')
FIELDS = ['path', 'logic', 'family', 'bytes', 'checks', 'sha256', 'split']
STATUS = re.compile(rb'\(\s*set-info\s+:status\s+(sat|unsat|unknown)\s*\)')


def sha256_file(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(block)
    return digest.hexdigest()


def recorded_environment(environment):
    return {name: value for name, value in environment.items()
            if name.startswith(('STP_', 'MIMALLOC_')) or name in
            ('LD_PRELOAD', 'OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS')}


def write_csv(path, rows, fields):
    with Path(path).open('w', newline='') as stream:
        writer = csv.DictWriter(stream, fieldnames=fields)
        writer.writeheader()
        writer.writerows(rows)


def select(args):
    root = Path(args.root).resolve()
    dest = Path(args.output).resolve()
    dest.mkdir(parents=True, exist_ok=True)
    if args.all:
        return select_all(args, root, dest)
    rows = []
    counts = {}
    logics = args.logics.split(',') if args.logics else (
        ['QF_BV', 'QF_ABV', 'QF_BVFP', 'QF_ABVFP'] if args.mode == 'incremental'
        else ['QF_BV', 'QF_ABV', 'QF_BVFP', 'QF_ABVFP', 'QF_FP'])
    for logic in logics:
        if not (root / logic).is_dir():
            continue
        for family in sorted((root / logic).iterdir()):
            if not family.is_dir():
                continue
            bins = [[], [], [], []]
            too_large = 0
            for file in family.rglob('*.smt2'):
                size = file.stat().st_size
                if size > args.max_mb * 1024 * 1024:
                    too_large += 1
                    continue
                bucket = 0 if size < 100_000 else 1 if size < 1_000_000 else 2 if size < 16_000_000 else 3
                relative = file.relative_to(root).as_posix()
                key = hashlib.sha256(f'{args.seed}:{relative}'.encode()).digest()
                bins[bucket].append((key, file, size))
            bins = [iter(sorted(b)) for b in bins]
            selected = []
            while len(selected) < args.per_family:
                found = False
                for bucket in bins:
                    for _, file, size in bucket:
                        data = file.read_bytes()
                        # Comments, strings, and quoted symbols may mention
                        # commands without executing them.
                        commands = NON_COMMAND.sub(b' ', data)
                        checks = len(CHECK.findall(commands))
                        if (args.mode == 'incremental' and checks < 2) or (
                                args.mode == 'non-incremental' and checks != 1):
                            continue
                        selected.append(dict(path=file.relative_to(root).as_posix(),
                                             logic=logic, family=family.name,
                                             bytes=size, checks=checks,
                                             sha256=hashlib.sha256(data).hexdigest(),
                                             split='evaluation'))
                        found = True
                        break
                    if len(selected) == args.per_family:
                        break
                if not found:
                    break
            # Reserve a fixed subset for tuning before running any solver.
            ranked = sorted(selected, key=lambda r: hashlib.sha256(
                f'training:{args.seed}:{r["path"]}'.encode()).digest())
            ntrain = min(max(1, len(ranked) // 5), max(0, len(ranked) - 1))
            for row in ranked[:ntrain]:
                row['split'] = 'training'
            rows.extend(selected)
            counts[f'{logic}/{family.name}'] = dict(selected=len(selected), training=ntrain,
                                                   excluded_over_size_limit=too_large)
    rows.sort(key=lambda r: r['path'])
    write_csv(dest / 'selection.csv', rows, FIELDS)
    for split in ['training', 'evaluation']:
        write_csv(dest / (split + '.csv'), [r for r in rows if r['split'] == split], FIELDS)
    (dest / 'selection.json').write_text(json.dumps(dict(root=str(root), seed=args.seed,
        per_family=args.per_family, max_mb=args.max_mb, mode=args.mode,
        logics=logics, families=counts), indent=2) + '\n')
    print(json.dumps(dict(total=len(rows), training=sum(r['split'] == 'training' for r in rows),
                          evaluation=sum(r['split'] == 'evaluation' for r in rows), families=counts), indent=2))


def select_all(args, root, dest):
    """Freeze every SMT-LIB input, including large or malformed files."""
    paths = sorted(root.rglob('*.smt2'))
    rows, counts, checks = [], defaultdict(int), defaultdict(int)
    for index, file in enumerate(paths):
        relative = file.relative_to(root)
        data = file.read_bytes()
        commands = NON_COMMAND.sub(b' ', data)
        count = len(CHECK.findall(commands))
        status = STATUS.search(commands) if count == 1 else None
        row = dict(path=relative.as_posix(), logic=relative.parts[0],
                   family=relative.parts[1] if len(relative.parts) > 2 else '.',
                   bytes=len(data), checks=count,
                   sha256=hashlib.sha256(data).hexdigest(), split='all',
                   declared_status=status[1].decode() if status else '')
        rows.append(row)
        counts[row['logic']] += 1
        checks[count] += 1
        if (index + 1) % 2000 == 0:
            print(f'Inventoried {index + 1}/{len(paths)} files', flush=True)
    # Mix theories and families throughout the campaign; no selection or caps.
    rows.sort(key=lambda r: hashlib.sha256(f'{args.seed}:{r["path"]}'.encode()).digest())
    if not rows:
        raise ValueError(f'no SMT-LIB files under {root}')
    write_csv(dest / 'selection.csv', rows, FIELDS + ['declared_status'])
    description = dict(root=str(root), seed=args.seed, mode='all', files=len(rows),
                       bytes=sum(r['bytes'] for r in rows), logics=dict(counts),
                       check_counts=dict(checks), excluded=0,
                       manifest_sha256=sha256_file(dest / 'selection.csv'))
    (dest / 'selection.json').write_text(json.dumps(description, indent=2) + '\n')
    print(json.dumps(description, indent=2), flush=True)


def run_one(binary, config, file, row, index, cpu, args, dest, environment):
    name = config['name']
    stem = f'logs/{cpu}/{index // 1000:04d}/{index:06d}-{name}'
    (dest / stem).parent.mkdir(parents=True, exist_ok=True)
    # The independent watchdog also survives a hard kill of this controller.
    cmd = ['timeout', '--signal=KILL', f'{args.timeout + 0.5}s', 'taskset', '-c', str(cpu)]
    cmd += ['prlimit', '--core=0']
    if args.memory_gb:
        cmd += [f'--as={int(args.memory_gb * 1024 ** 3)}']
    cmd += ['--']
    cmd += [str(binary)] + config['args'] + [str(file)]
    started = time.monotonic()
    with (dest / (stem + '.stdout')).open('wb') as stdout, (dest / (stem + '.stderr')).open('wb') as stderr:
        process = subprocess.Popen(cmd, stdout=stdout, stderr=stderr,
                                   start_new_session=True, env=environment)
        timed_out = False

        def expire():
            nonlocal timed_out
            if process.poll() is None:
                timed_out = True
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass

        # wait(timeout=...) polls in Python and can round a short run up by
        # tens of milliseconds. A watchdog lets wait() use blocking waitpid.
        timer = threading.Timer(max(0, args.timeout - (time.monotonic() - started)), expire)
        timer.start()
        returncode = process.wait()
        timer.cancel()
        timer.join()
    seconds = time.monotonic() - started
    timed_out = timed_out or returncode in (124, 137)
    output = (dest / (stem + '.stdout')).read_text(errors='replace')
    answers = [line.strip() for line in output.splitlines() if line.strip() in ['sat', 'unsat', 'unknown']]
    output_error = any(line.lstrip().startswith('(error') for line in output.splitlines())
    expected = int(row['checks'])
    wrong_answer = (expected == 1 and row.get('declared_status') in ('sat', 'unsat')
                    and any(a in ('sat', 'unsat') and a != row['declared_status'] for a in answers))
    completed = (not timed_out and returncode == 0 and expected > 0 and len(answers) == expected
                 and 'unknown' not in answers and not output_error)
    completed = completed and not wrong_answer
    status = 'solved' if completed else 'timeout' if timed_out else 'unknown' if 'unknown' in answers else 'error'
    return dict(path=row['path'], logic=row['logic'], family=row['family'], solver=name,
                seconds=seconds, par2=seconds if completed else 2 * args.timeout,
                status=status, returncode=returncode, expected_checks=int(row['checks']),
                answered_checks=len(answers), answers=answers, cpu=cpu,
                stdout=stem + '.stdout', stderr=stem + '.stderr', wrong_answer=wrong_answer)


def summarize(rows, dest, cutoff, expected=None, label='complete'):
    solvers = sorted({r['solver'] for r in rows})
    summary = {}
    by_solver, by_path = defaultdict(list), defaultdict(list)
    for row in rows:
        by_solver[row['solver']].append(row)
        by_path[row['path']].append(row)
    table = []
    for solver in solvers:
        groups = defaultdict(list)
        for row in by_solver[solver]:
            groups[('all', 'all')].append(row)
            groups[('logic', row['logic'])].append(row)
            groups[('family', row['logic'] + '/' + row['family'])].append(row)
        family, logics = {}, {}
        for (scope, name), group in sorted(groups.items()):
            values = dict(n=len(group), solved=sum(r['status'] == 'solved' for r in group),
                          timeouts=sum(r['status'] == 'timeout' for r in group),
                          errors=sum(r['status'] == 'error' for r in group),
                          unknown=sum(r['status'] == 'unknown' for r in group),
                          wrong_answers=sum(r.get('wrong_answer', False) for r in group),
                          par2_sum=sum(r['par2'] for r in group))
            values['par2_mean'] = values['par2_sum'] / values['n']
            table.append(dict(solver=solver, scope=scope, group=name, **values))
            if scope == 'all':
                summary[solver] = values
            elif scope == 'logic':
                logics[name] = values
            else:
                family[name] = values
        summary[solver] = dict(summary[solver], families=family, logics=logics)
    # A SAT/UNSAT disagreement invalidates the comparison, including answers
    # printed before a timed-out session stopped. UNKNOWN is not a verdict.
    disagreements = []
    for path, own in sorted(by_path.items()):
        for a, b in itertools.combinations(own, 2):
            for query, (x, y) in enumerate(zip(a['answers'], b['answers']), 1):
                if x != 'unknown' and y != 'unknown' and x != y:
                    disagreements.append(dict(path=path, query=query, solvers=[a['solver'], b['solver']], answers=[x, y]))
    result = dict(timeout=cutoff, unit='complete SMT-LIB session', state=label,
                  expected_observations=expected, observed=len(rows), solvers=summary,
                  disagreements=disagreements,
                  valid=not disagreements and not any(r.get('wrong_answer', False) for r in rows))
    prefix = '' if label == 'complete' else 'progress-'
    (dest / (prefix + 'summary.json')).write_text(json.dumps(result, indent=2) + '\n')
    if rows:
        write_csv(dest / (prefix + 'par2.csv'), table, list(table[0]))
    if rows and label == 'complete':
        write_csv(dest / 'results.csv', [{k: v for k, v in r.items() if k != 'answers'} for r in rows],
                  [k for k in rows[0] if k != 'answers'])
    print(json.dumps(dict(timeout=cutoff, solvers={s: {k: v for k, v in v.items() if k not in ('families', 'logics')}
                        for s, v in summary.items()}, state=label,
                          observed=len(rows), expected_observations=expected,
                          disagreements=disagreements), indent=2))
    return result['valid']


def read_journals(dest, repair=False):
    rows, seen = [], set()
    for path in sorted(dest.glob('cpu-*.jsonl')):
        mode = 'r+b' if repair else 'rb'
        with path.open(mode) as stream:
            while True:
                start = stream.tell()
                line = stream.readline()
                if not line:
                    break
                if not line.endswith(b'\n'):
                    if repair:
                        stream.truncate(start)
                    break  # A live writer can have an unfinished last line.
                row = json.loads(line)
                key = (row['path'], row['solver'])
                if key in seen:
                    raise ValueError(f'duplicate observation: {key}')
                seen.add(key)
                rows.append(row)
    return rows


def progress(args):
    dest = Path(args.output).resolve()
    metadata = json.loads((dest / 'metadata.json').read_text())
    rows = read_journals(dest)
    expected = metadata['files'] * len(metadata['configurations'])
    summarize(rows, dest, metadata['timeout'], expected,
              'complete' if len(rows) == expected else 'incomplete')


def run(args):
    binary = Path(args.binary).resolve()
    root = Path(args.root).resolve()
    dest = Path(args.output).resolve()
    if args.resume:
        if not (dest / 'metadata.json').is_file():
            raise ValueError('--resume requires an existing campaign')
    else:
        dest.mkdir(parents=True, exist_ok=False)
    # Refuse overlapping controllers writing or resuming the same campaign.
    with (dest / 'run.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        return run_locked(args, binary, root, dest)


def run_locked(args, binary, root, dest):
    # Snapshot the executable and its local shared libraries so rebuilds during
    # an experiment cannot silently replace the implementation being measured.
    snapshot = dest / 'bin' / binary.name
    environment = os.environ.copy()
    environment['LD_LIBRARY_PATH'] = str(dest / 'lib') + ':' + environment.get('LD_LIBRARY_PATH', '')
    rows = list(csv.DictReader(Path(args.manifest).open()))
    configs = json.loads(Path(args.configs).read_text())
    if not configs or len({c['name'] for c in configs}) != len(configs):
        raise ValueError('configuration names must be unique')
    for config in configs:
        if not re.fullmatch(r'[a-zA-Z0-9_-]+', config['name']):
            raise ValueError('configuration name must be a safe filename component')
    cpus = [int(x) for x in args.cpus.split(',')] if args.cpus else sorted(os.sched_getaffinity(0))[:args.workers]
    if (args.workers < 1 or args.timeout <= 0 or args.memory_gb < 0 or
            len(cpus) < args.workers or len(set(cpus)) != len(cpus) or
            not set(cpus).issubset(os.sched_getaffinity(0))):
        raise ValueError('invalid workers, cutoff, memory cap, or CPU assignments')
    if not rows or len({r['path'] for r in rows}) != len(rows):
        raise ValueError('manifest must contain unique inputs')
    if any(Path(r['path']).is_absolute() or '..' in Path(r['path']).parts for r in rows):
        raise ValueError('manifest paths must stay inside the input root')
    runner_hash = sha256_file(Path(__file__))
    if args.resume:
        metadata = json.loads((dest / 'metadata.json').read_text())
        required = dict(root=str(root), timeout=args.timeout, memory_gb=args.memory_gb,
                        configurations=configs, runner_sha256=runner_hash,
                        environment=recorded_environment(environment))
        if any(metadata.get(k) != v for k, v in required.items()):
            raise ValueError('resume would change the recorded experiment')
        if Path(args.manifest).read_bytes() != (dest / 'manifest.csv').read_bytes():
            raise ValueError('resume manifest differs from the frozen manifest')
        if sha256_file(snapshot) != metadata['binary_sha256']:
            raise ValueError('snapshot executable changed')
        for path, digest in metadata['snapshot_libraries'].items():
            if sha256_file(dest / path) != digest:
                raise ValueError(f'snapshot library changed: {path}')
        for path, digest in metadata['linked_libraries'].items():
            if path.startswith(('/lib/', '/lib64/', '/usr/lib/', '/usr/lib64/')) and sha256_file(path) != digest:
                raise ValueError(f'system library changed since the original run: {path}')
        existing = read_journals(dest, repair=True)
    else:
        (dest / 'bin').mkdir()
        (dest / 'lib').mkdir()
        shutil.copy2(binary, snapshot)
        linked, snapshot_libraries = {}, {}
        for line in subprocess.check_output(['ldd', str(binary)], text=True).splitlines():
            match = re.search(r'=> (/\S+)', line)
            if match:
                library = Path(match[1])
                digest = sha256_file(library)
                linked[str(library)] = digest
                if not match[1].startswith(('/lib/', '/lib64/', '/usr/lib/', '/usr/lib64/')):
                    target = dest / 'lib' / library.name
                    shutil.copy2(library, target)
                    snapshot_libraries[target.relative_to(dest).as_posix()] = digest
        shutil.copy2(Path(__file__), dest / 'runner.py')
        metadata = dict(binary=str(binary), root=str(root), binary_sha256=sha256_file(snapshot),
                        runner_sha256=runner_hash, linked_libraries=linked,
                        snapshot_libraries=snapshot_libraries,
                        version=subprocess.check_output([str(snapshot), '--version'], text=True, env=environment),
                        host=platform.uname()._asdict(), cpus=cpus, workers=args.workers,
                        timeout=args.timeout, memory_gb=args.memory_gb, configurations=configs,
                        environment=recorded_environment(environment),
                        files=len(rows), manifest=str(Path(args.manifest).resolve()),
                        start_time=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()))
        (dest / 'metadata.json').write_text(json.dumps(metadata, indent=2) + '\n')
        (dest / 'manifest.csv').write_bytes(Path(args.manifest).read_bytes())
        existing = []
    row_by_path = {r['path']: r for r in rows}
    names = {c['name'] for c in configs}
    completed_keys = set()
    for observation in existing:
        row = row_by_path.get(observation['path'])
        if row is None or observation['solver'] not in names:
            raise ValueError('journal does not match the frozen inputs/configurations')
        if observation['expected_checks'] != int(row['checks']):
            raise ValueError('journal query count differs from the manifest')
        score = observation['seconds'] if observation['status'] == 'solved' else 2 * args.timeout
        if observation['par2'] != score:
            raise ValueError('journal PAR2 differs from the recorded outcome')
        for key in ('stdout', 'stderr'):
            if not (dest / observation[key]).is_file():
                raise ValueError('captured observation log is missing')
        completed_keys.add((observation['path'], observation['solver']))
    assignments = iter(enumerate(rows))
    assignment_lock, stop = threading.Lock(), threading.Event()
    previous_handlers = {}

    def halt(signum, frame):
        stop.set()
        print('Stopping after active solves finish; use --resume to continue.', flush=True)

    for signum in (signal.SIGTERM, signal.SIGINT):
        previous_handlers[signum] = signal.signal(signum, halt)
    (dest / 'state.json').write_text(json.dumps(dict(state='running', pid=os.getpid(),
        observed=len(existing), expected=len(rows) * len(configs), cpus=cpus[:args.workers])) + '\n')

    def worker(cpu):
        completed = []
        while not stop.is_set():
            with assignment_lock:
                try:
                    index, row = next(assignments)
                except StopIteration:
                    break
            pending = [c for c in configs if (row['path'], c['name']) not in completed_keys]
            if not pending:
                continue
            file = root / row['path']
            if sha256_file(file) != row['sha256']:
                stop.set()
                raise ValueError(f'benchmark changed: {file}')
            # Rotate all four positions rather than only reversing the order.
            pivot = index % len(configs)
            order = configs[pivot:] + configs[:pivot]
            pair = []
            with (dest / f'cpu-{cpu}.jsonl').open('a') as stream:
                for config in order:
                    if stop.is_set():
                        break
                    if (row['path'], config['name']) in completed_keys:
                        continue
                    result = run_one(snapshot, config, file, row, index, cpu, args, dest, environment)
                    stream.write(json.dumps(result) + '\n')
                    stream.flush()
                    pair.append(result)
                    completed.append(result)
            print(f'{index + 1}/{len(rows)} ' + ' '.join(f'{r["solver"]}={r["status"]}:{r["seconds"]:.3f}s' for r in pair) + ' ' + row['path'], flush=True)
        return completed

    results = existing
    try:
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
            futures = [pool.submit(worker, cpus[i]) for i in range(args.workers)]
            for future in concurrent.futures.as_completed(futures):
                try:
                    results.extend(future.result())
                except BaseException:
                    stop.set()
                    raise
    finally:
        for signum, handler in previous_handlers.items():
            signal.signal(signum, handler)
    results.sort(key=lambda r: (r['path'], r['solver']))
    expected = len(rows) * len(configs)
    label = 'complete' if len(results) == expected else 'incomplete'
    (dest / 'state.json').write_text(json.dumps(dict(state=label, observed=len(results),
        expected=expected, end_time=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()))) + '\n')
    valid = summarize(results, dest, args.timeout, expected, label)
    if label != 'complete':
        print('Campaign incomplete; resume with the same configuration and --resume.', flush=True)
        return None
    if not valid:
        raise SystemExit('SAT/UNSAT disagreement: inspect summary.json')
    return results, dest, args.timeout


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    choose = sub.add_parser('select')
    choose.add_argument('--root', required=True)
    choose.add_argument('--output', required=True)
    choose.add_argument('--seed', type=int, default=20261012)
    choose.add_argument('--per-family', type=int, default=16)
    choose.add_argument('--max-mb', type=int, default=64)
    choose.add_argument('--mode', choices=['incremental', 'non-incremental'], default='incremental')
    choose.add_argument('--logics', help='comma-separated logic directories; defaults depend on --mode')
    choose.add_argument('--all', action='store_true',
                        help='include every .smt2 under root; no sampling, size cap, or training split')
    launch = sub.add_parser('run')
    launch.add_argument('--root', required=True)
    launch.add_argument('--manifest', required=True)
    launch.add_argument('--binary', required=True)
    launch.add_argument('--configs', required=True)
    launch.add_argument('--output', required=True)
    launch.add_argument('--timeout', type=float, default=60)
    launch.add_argument('--workers', type=int, default=4)
    launch.add_argument('--cpus')
    launch.add_argument('--memory-gb', type=float, default=8)
    launch.add_argument('--resume', action='store_true', help='continue the frozen campaign without rerunning recorded observations')
    status = sub.add_parser('status', help='summarize recorded observations; incomplete scores are labeled as progress')
    status.add_argument('--output', required=True)
    args = parser.parse_args(argv)
    if args.command == 'select':
        return select(args)
    return progress(args) if args.command == 'status' else run(args)


if __name__ == '__main__':
    main()
