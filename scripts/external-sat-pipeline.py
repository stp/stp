#!/usr/bin/env python3
"""Diagnostic: STP encoding, optional Satsuma CLI, then a one-shot SAT binary."""
import argparse
from pathlib import Path
import re
import subprocess
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--stp', required=True)
    parser.add_argument('--satsuma', required=True)
    parser.add_argument('--solver', required=True)
    parser.add_argument('--mode', choices=('off', 'fix'), required=True)
    parser.add_argument('--workdir', type=Path, required=True)
    parser.add_argument('--verify-model', action='store_true')
    parser.add_argument('input')
    args = parser.parse_args()
    work = args.workdir.resolve()
    with (work / 'encoding.stdout').open('w') as out:
        encoded = subprocess.run([args.stp, '--kissat', '--incremental=off',
            '--cnf-generation-effort=new-medium', '--output-CNF', '--exit-after-CNF',
            args.input], cwd=work, stdout=out)
    if encoded.returncode:
        return 1
    cnfs = sorted(work.glob('output_*.cnf'))
    if not cnfs:
        answers = [x for x in (work / 'encoding.stdout').read_text().splitlines()
                   if x in ('sat', 'unsat')]
        if len(answers) == 1:
            print(answers[0])
            return 0
        raise RuntimeError('encoding produced neither a CNF nor a verdict')
    if len(cnfs) != 1:
        raise RuntimeError('diagnostic requires one complete CNF')
    original = cnfs[0]
    cnf = original
    if args.mode == 'fix':
        cnf = work / 'preprocessed.cnf'
        result = subprocess.run([args.satsuma, 'fix', str(original), '--silent',
            '--full-skip-limit', '100000000', '--add-reduced-as-unit',
            '--out-file', str(cnf)], stdout=subprocess.DEVNULL)
        if result.returncode:
            return 1
    with (work / 'solver.stdout').open('w') as out:
        result = subprocess.run([args.solver, str(cnf)], stdout=out)
    output = (work / 'solver.stdout').read_text()
    if result.returncode == 20 and re.search(r'^s UNSATISFIABLE$', output, re.M):
        print('unsat')
        return 0
    if result.returncode != 10 or not re.search(r'^s SATISFIABLE$', output, re.M):
        raise RuntimeError(f'SAT solver exit {result.returncode}: {output[-1000:]}')
    if args.verify_model:
        assignment = {}
        for line in output.splitlines():
            if line.startswith('v '):
                for token in line[2:].split():
                    literal = int(token)
                    if literal:
                        assignment[abs(literal)] = literal > 0
        satisfied = False
        with original.open() as source:
            for line in source:
                if line.startswith(('c', 'p')):
                    continue
                for token in line.split():
                    literal = int(token)
                    if literal:
                        satisfied |= assignment.get(abs(literal)) == (literal > 0)
                    else:
                        if not satisfied:
                            raise RuntimeError('SAT witness violates the original CNF')
                        satisfied = False
    print('sat')
    return 0


if __name__ == '__main__':
    sys.exit(main())
