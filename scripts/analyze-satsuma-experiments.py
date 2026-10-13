#!/usr/bin/env python3
"""Audit a completed SAT benchmark and calculate paired PAR2 comparisons."""
import argparse
from collections import defaultdict
import csv
import hashlib
import json
from pathlib import Path
import re

import numpy as np


def analyze(run, baseline, repetitions, seed):
    metadata = json.loads((run / 'metadata.json').read_text())
    manifest = list(csv.DictReader(Path(metadata['manifest']).open()))
    configurations = [c['name'] for c in metadata['configurations']]
    if baseline not in configurations:
        raise ValueError(f'unknown baseline {baseline}')
    grouped = defaultdict(dict)
    for journal in sorted(run.glob('cpu-*.jsonl')):
        for line in journal.read_text().splitlines():
            row = json.loads(line)
            if row['solver'] in grouped[row['path']]:
                raise ValueError(f'duplicate observation: {row["path"]}')
            grouped[row['path']][row['solver']] = row
    paths = [r['path'] for r in manifest]
    if set(grouped) != set(paths) or any(
            set(grouped[p]) != set(configurations) for p in paths):
        raise ValueError('run is incomplete or does not match its manifest')

    disagreements, status_errors, input_errors = [], [], []
    known = defaultdict(list)
    root = Path(metadata['root'])
    for row in manifest:
        path = row['path']
        data = (root / path).read_bytes()
        if hashlib.sha256(data).hexdigest() != row['sha256']:
            input_errors.append(path)
        # Strip comments before inspecting a declared SMT-LIB status.
        commands = re.sub(rb'"(?:[^"]|"")*"|\|[^|]*\||;[^\n]*', b' ', data)
        declared = re.search(rb'\(\s*set-info\s+:status\s+(sat|unsat)\s*\)', commands)
        declared = declared[1].decode() if declared else None
        if declared:
            known[declared].append(path)
        answers = {r['answers'][0] for r in grouped[path].values()
                   if r['answers'] and r['answers'][0] in ('sat', 'unsat')}
        if len(answers) > 1:
            disagreements.append(path)
        if declared:
            for name, observation in grouped[path].items():
                if any(a in ('sat', 'unsat') and a != declared
                       for a in observation['answers']):
                    status_errors.append(dict(path=path, solver=name,
                                              declared=declared,
                                              answers=observation['answers']))

    families = sorted({r['family'] for r in manifest})
    family_indices = {f: [i for i, r in enumerate(manifest) if r['family'] == f]
                      for f in families}
    rng = np.random.default_rng(seed)
    resamples = rng.integers(0, len(families), size=(repetitions, len(families)))
    base = np.array([grouped[p][baseline]['par2'] for p in paths])
    base_solved = np.array([grouped[p][baseline]['status'] == 'solved' for p in paths])
    base_family_sum = np.array([base[family_indices[f]].sum() for f in families])
    comparisons = {}
    for name in configurations:
        own = [grouped[p][name] for p in paths]
        values = np.array([r['par2'] for r in own])
        solved = np.array([r['status'] == 'solved' for r in own])
        both = solved & base_solved
        family_sum = np.array([values[family_indices[f]].sum() for f in families])
        boot_ratio = family_sum[resamples].sum(axis=1) / base_family_sum[resamples].sum(axis=1)
        by_family = []
        for f in families:
            indices = family_indices[f]
            by_family.append(dict(family=f, n=len(indices),
                solved=int(solved[indices].sum()),
                baseline_solved=int(base_solved[indices].sum()),
                par2_mean=float(values[indices].mean()),
                baseline_par2_mean=float(base[indices].mean()),
                total_seconds_saved=float((base[indices] - values[indices]).sum())))
        errors = []
        for row in own:
            if row['status'] == 'error':
                stdout = (run / row['stdout']).read_text(errors='replace')
                stderr = (run / row['stderr']).read_text(errors='replace')
                errors.append(dict(path=row['path'], returncode=row['returncode'],
                    reason='segmentation fault' if row['returncode'] == -11 else
                    'resource' if 'RESOURCE' in stdout + stderr else 'other',
                    output_tail=(stdout + stderr)[-1000:]))
        comparisons[name] = dict(n=len(paths), solved=int(solved.sum()),
            timeouts=sum(r['status'] == 'timeout' for r in own),
            errors=len(errors), unknown=sum(r['status'] == 'unknown' for r in own),
            par2_mean=float(values.mean()),
            par2_ratio_to_baseline=float(values.sum() / base.sum()),
            par2_ratio_family_bootstrap_95_ci=np.quantile(boot_ratio, [0.025, 0.975]).tolist(),
            common_solved=int(both.sum()),
            common_solved_geomean_ratio=float(np.exp(np.log(values[both] / base[both]).mean()))
                if both.any() else None,
            gained_solutions=[p for i, p in enumerate(paths) if solved[i] and not base_solved[i]],
            lost_solutions=[p for i, p in enumerate(paths) if base_solved[i] and not solved[i]],
            declared_sat_solved=sum(grouped[p][name]['status'] == 'solved' for p in known['sat']),
            declared_unsat_solved=sum(grouped[p][name]['status'] == 'solved' for p in known['unsat']),
            families=by_family, error_details=errors)
    return dict(run=str(run), baseline=baseline, timeout=metadata['timeout'],
        memory_gb=metadata['memory_gb'], files=len(paths), families=len(families),
        weighting='one weight per selected file; families sampled as clusters for confidence intervals',
        bootstrap_repetitions=repetitions, bootstrap_seed=seed,
        declared_status_counts={key: len(value) for key, value in known.items()},
        answer_disagreements=disagreements, declared_status_errors=status_errors,
        changed_inputs=input_errors, comparisons=comparisons)


def plot(run, output):
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    metadata = json.loads((run / 'metadata.json').read_text())
    groups = defaultdict(list)
    for journal in run.glob('cpu-*.jsonl'):
        for line in journal.read_text().splitlines():
            row = json.loads(line)
            if row['status'] == 'solved':
                groups[row['solver']].append(row['seconds'])
    fig, ax = plt.subplots(figsize=(8.5, 5))
    for config in metadata['configurations']:
        times = sorted(groups[config['name']])
        ax.step(times, np.arange(1, len(times) + 1), where='post',
                label=f'{config["name"]} ({len(times)})')
    ax.set_xscale('log')
    ax.set_xlim(0.01, metadata['timeout'])
    ax.set_xlabel('Complete SMT-LIB session wall time in seconds')
    ax.set_ylabel('Sessions solved')
    ax.set_title(f'QF_BV comparison at {metadata["timeout"]:g} seconds')
    ax.grid(True, alpha=0.2)
    ax.legend(loc='lower right')
    fig.tight_layout()
    for suffix in ('.svg', '.png', '.pdf'):
        fig.savefig(output.with_suffix(suffix), dpi=160)
    plt.close(fig)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', required=True, type=Path)
    parser.add_argument('--baseline', default='kissat')
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--bootstrap-repetitions', default=10000, type=int)
    parser.add_argument('--seed', default=2026101402, type=int)
    parser.add_argument('--plot', type=Path)
    args = parser.parse_args()
    result = analyze(args.run.resolve(), args.baseline, args.bootstrap_repetitions, args.seed)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    for name, row in result['comparisons'].items():
        print(name, f'{row["solved"]}/{row["n"]}',
              f'PAR2={row["par2_mean"]:.5f}',
              f'ratio={row["par2_ratio_to_baseline"]:.5f}',
              f'95% CI={row["par2_ratio_family_bootstrap_95_ci"]}',
              f'errors={row["errors"]}')
    if args.plot:
        plot(args.run, args.plot)
    if result['answer_disagreements'] or result['declared_status_errors'] or result['changed_inputs']:
        raise SystemExit('benchmark audit failed; see the analysis JSON')


if __name__ == '__main__':
    main()
