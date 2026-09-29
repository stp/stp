"""SMT-LIB command protocol checks that need separate channels or files."""

from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SOLVER = str(Path(sys.argv.pop(1)).resolve())


def run(source, cwd=None):
    return subprocess.run([SOLVER], input=source, text=True,
                          capture_output=True, cwd=cwd, timeout=30)


class OutputChannels(unittest.TestCase):
    def test_defaults_and_standard_channels(self):
        result = run('''
(get-option :regular-output-channel)
(get-option :diagnostic-output-channel)
(set-option :print-success true)
(set-option :regular-output-channel "stdout")
(set-option :diagnostic-output-channel "stderr")
(echo "done")
''')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout,
                         '"stdout"\n"stderr"\nsuccess\nsuccess\nsuccess\n"done"\n')
        self.assertEqual(result.stderr, '')

    def test_regular_file_appends_and_reset_restores_defaults(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'responses.out'
            path.write_text('existing\n')
            result = run('''
(set-option :print-success true)
(set-option :regular-output-channel "responses.out")
(get-option :regular-output-channel)
(echo "first")
(set-logic QF_BV)
(check-sat)
(set-option :regular-output-channel "stdout")
(set-option :regular-output-channel "responses.out")
(echo "second")
(reset)
(get-option :regular-output-channel)
(get-option :diagnostic-output-channel)
(echo "back")
''', tmp)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout,
                             'success\nsuccess\n"stdout"\n"stderr"\n"back"\n')
            self.assertEqual(path.read_text(),
                             'existing\nsuccess\n"responses.out"\n"first"\n'
                             'success\nsat\nsuccess\n"second"\n')

    def test_diagnostics_use_selected_file(self):
        with tempfile.TemporaryDirectory() as tmp:
            result = run('''
(set-option :diagnostic-output-channel "diagnostics.out")
(set-logic QF_BV)
(set-info :status unsat)
(assert true)
(check-sat)
''', tmp)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout, 'sat\n')
            self.assertEqual(result.stderr, '')
            self.assertIn('Expected unsatisfiable, FOUND satisfiable',
                          (Path(tmp) / 'diagnostics.out').read_text())

    def test_regular_can_use_stderr(self):
        result = run('''
(set-option :regular-output-channel "stderr")
(echo "other channel")
''')
        self.assertEqual(result.returncode, 0)
        self.assertEqual(result.stdout, '')
        self.assertEqual(result.stderr, '"other channel"\n')

    def test_failed_open_reports_error_on_previous_channel(self):
        with tempfile.TemporaryDirectory() as tmp:
            result = run('''
(set-option :regular-output-channel "missing/directory/out")
(echo "unreachable")
''', tmp)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout,
                             '(error "cannot open output channel: missing/directory/out")\n')


if __name__ == '__main__':
    unittest.main()
