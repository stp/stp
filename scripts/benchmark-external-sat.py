#!/usr/bin/env python3
"""Use the existing benchmark runner for external SAT diagnostic pipelines."""
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import sys


ROOT = Path(__file__).resolve().parents[1]
SOURCE = Path('/home/avj/clones/stp/master/scripts/benchmark-sat-backends.py')
spec = importlib.util.spec_from_file_location('stp_sat_benchmark', SOURCE)
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)
original_run_one = runner.run_one
components = ROOT / 'build-experiments/external-components'
components.mkdir(exist_ok=True)
sources = {
    'driver.py': ROOT / 'scripts/external-sat-pipeline.py',
    'kissat': Path('/tmp/anders/satsuma-iter-kissat/src/solver/kissat/build/kissat'),
    'ae': Path('/tmp/anders/satsuma-iter-kissat/src/solver/AE_kissat2025_MAB/build/kissat'),
    'satsuma': ROOT / 'build-experiments/satsuma-install/bin/satsuma',
}
hashes = {}
provenance = components / 'provenance.json'
if provenance.exists():
    hashes = json.loads(provenance.read_text())
    for name, expected in hashes.items():
        actual = hashlib.sha256((components / name).read_bytes()).hexdigest()
        if actual != expected:
            raise RuntimeError(f'archived diagnostic component changed: {name}')
else:
    for name, source in sources.items():
        dest = components / name
        shutil.copy2(source, dest)
        hashes[name] = hashlib.sha256(dest.read_bytes()).hexdigest()
    provenance.write_text(json.dumps(hashes, indent=2) + '\n')


def run_one(binary, config, file, row, index, cpu, args, dest, environment):
    work = dest / f'{index:04d}-{config["name"]}.work'
    work.mkdir()
    call = dict(config)
    call['args'] = [str(components / 'driver.py'), '--stp', str(binary),
        '--satsuma', str(components / 'satsuma'), '--solver',
        str(components / config['engine']), '--mode', config['mode'],
        '--workdir', str(work)]
    try:
        return original_run_one(Path(sys.executable), call, file, row, index,
                                cpu, args, dest, environment)
    finally:
        shutil.rmtree(work)


runner.run_one = run_one
if __name__ == '__main__':
    runner.main()
