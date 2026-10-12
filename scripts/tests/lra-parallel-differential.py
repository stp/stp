#!/usr/bin/env python3
"""Check the LRA differential fuzzer's failure gates with synthetic commands."""

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


FUZZ = Path(__file__).resolve().parents[1] / 'fuzz/lra-parallel-differential.py'


class DifferentialTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix='stpp-fuzz-test-')
        self.addCleanup(self.temporary.cleanup)
        self.base = Path(self.temporary.name)

    def command(self, name, report, *, answer="'sat'"):
        binary = self.base / (name + '.py')
        binary.write_text(
            f'#!{sys.executable}\n'
            'import json,sys\n'
            'from pathlib import Path\n'
            'if "--version" in sys.argv:\n'
            ' print("synthetic stp-p"); raise SystemExit(0)\n'
            'report_path=Path(sys.argv[sys.argv.index("--stats-json")+1])\n'
            f'answer={answer}\n'
            f'report={report!r}\n'
            'report["answer"]=answer\n'
            'report_path.write_text(json.dumps(report))\n'
            'print(answer)\n'
            'raise SystemExit({"sat":10,"unsat":20,"unknown":0}[answer])\n')
        binary.chmod(0o755)
        return binary

    def test_differential_checks_hedge_failures_and_verdicts(self):
        # Only report handling is under test: both executables are synthetic.
        oracle = self.base / 'oracle.py'
        oracle.write_text(f'#!{sys.executable}\nimport sys\n'
                          'print("synthetic oracle" if "--version" in sys.argv else "sat")\n')
        oracle.chmod(0o755)
        cases = [
            ('success', {'wait_status': 0, 'answer': 'sat', 'reported': 'sat',
                         'report': {'answer': 'sat'}}, True),
            ('error', {'wait_status': 0, 'report': {'error': 'helper failed'}}, False),
            ('bad-exit', {'wait_status': 256}, False),
            ('unexpected-kill', {'wait_status': 9}, False),
            ('missing-report', {'wait_status': 0}, False),
            ('wrong-answer', {'wait_status': 0, 'answer': 'unsat', 'reported': 'unsat',
                              'report': {'answer': 'unsat'}}, False),
            ('cleanup', {'wait_status': 9, 'killed': True}, True),
        ]
        for name, hedge, accepted in cases:
            with self.subTest(name=name):
                hedge.update(role='hedge', forked=True)
                self.command('fuzz-' + name, {'hedge': hedge})
                output = self.base / ('fuzz-output-' + name)
                command = [sys.executable, str(FUZZ), '--binary',
                           str(self.base / ('fuzz-' + name + '.py')), '--z3', str(oracle),
                           '--output', str(output), '--count', '1', '--jobs', '1',
                           '--configs', 'default', '--timeout', '1',
                           '--worker-mib', '0', '--memory-mib', '0']
                result = subprocess.run(command, capture_output=True, text=True, timeout=15)
                self.assertEqual(result.returncode == 0, accepted, result.stdout + result.stderr)
                rows = [json.loads(s) for s in (output / 'results.jsonl').read_text().splitlines()]
                self.assertEqual(bool(rows[-1]['failures']), not accepted)
                if name == 'success':
                    self.assertEqual(rows[-1]['children_decided'], 1)
                    self.assertEqual(rows[-1]['children_reported'], 1)

    @unittest.skipUnless(len(os.sched_getaffinity(0)) >= 2, 'requires two allowed CPUs')
    def test_differential_public_mode_uses_public_defaults(self):
        oracle = self.base / 'oracle.py'
        oracle.write_text(f'#!{sys.executable}\nimport sys\n'
                          'print("synthetic oracle" if "--version" in sys.argv else "sat")\n')
        oracle.chmod(0o755)
        self.command('public-fuzz', {})
        output = self.base / 'public-fuzz-output'
        command = [sys.executable, str(FUZZ), '--public', '--binary',
                   str(self.base / 'public-fuzz.py'), '--z3', str(oracle),
                   '--output', str(output), '--count', '1', '--jobs', '1,2',
                   '--timeout', '1', '--worker-mib', '0', '--memory-mib', '0']
        result = subprocess.run(command, capture_output=True, text=True, timeout=15)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        config = json.loads((output / 'config.json').read_text())
        self.assertTrue(config['public'])
        self.assertTrue(config['first_answer'])
        self.assertEqual(config['configs'], 'default')
        rows = [json.loads(s) for s in (output / 'results.jsonl').read_text().splitlines()]
        self.assertEqual({r['jobs'] for r in rows}, {1, 2})
        allowed = {'--config', '--timeout', '--stats-json', '--worker-memory-mib',
                   '--memory-mib'}
        for row in rows:
            self.assertFalse(row['failures'])
            self.assertEqual({a for a in row['command'] if a.startswith('--')}, allowed)
            self.assertEqual(row['config'], 'default')
        for extra in (['--configs', 'lra-exact'], ['--extra=--control', '--extra=batch-all']):
            result = subprocess.run(command + extra, capture_output=True, text=True, timeout=15)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('public mode takes only public', result.stderr)


if __name__ == '__main__':
    unittest.main()
