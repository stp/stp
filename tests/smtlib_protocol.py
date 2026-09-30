"""SMT-LIB command protocol checks that need separate channels or files."""

from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest

SOLVER = str(Path(sys.argv.pop(1)).resolve())


def run(source, cwd=None, args=()):
    return subprocess.run([SOLVER, *args], input=source, text=True,
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


class CommandModes(unittest.TestCase):
    def assert_error(self, source, message):
        result = run(source + '\n(echo "unreachable")\n')
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('(error "' + message, result.stdout)
        self.assertNotIn('unreachable', result.stdout)

    def test_logic_may_be_omitted(self):
        for source in [
                '(assert true)',
                '(declare-const p Bool)(assert p)',
                '(declare-fun x () (_ BitVec 8))(assert (= x #x2a))',
                '(declare-const x Float32)(assert (fp.isNaN x))',
                '(declare-const x Real)(assert (= x (/ 1 3)))',
                '(declare-sort S 0)(declare-const x S)(assert (= x x))',
                '(declare-fun f (Bool) Bool)(assert (f true))',
                '(define-sort Byte () (_ BitVec 8))(declare-const x Byte)',
                '(define-fun f ((x Real)) Real (+ x 1))(assert (= (f 1) 2))',
                '(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))'
                '(declare-const b (Array (_ BitVec 8) (_ BitVec 8)))'
                '(assert (= a b))',
                '(push 1)(assert false)(pop 1)',
                '(push 1)(set-logic QF_BV)(pop 1)',
                '(set-logic QF_BV)(reset)(declare-const x Float32)',
                '']:
            with self.subTest(source=source):
                result = run(source + '(check-sat)')
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual(result.stdout, 'sat\n')

    def test_logic_cannot_change_after_selection(self):
        self.assert_error('(set-logic QF_BV)(set-logic QF_BV)',
                          'set-logic is not permitted')
        self.assert_error('(declare-const x Bool)(set-logic QF_BV)',
                          'set-logic is not permitted')

    def test_options_before_or_after_logic(self):
        options = '''
(set-option :produce-models true)
(set-option :produce-assignments true)
(set-option :produce-assertions true)
(set-option :global-declarations true)
(set-option :produce-unsat-assumptions true)
(set-option :produce-unsat-cores true)
'''
        for prefix in [options + '(set-logic QF_BV)',
                       '(set-logic QF_BV)' + options]:
            with self.subTest(prefix=prefix):
                result = run(prefix + '''
(push 1)
(declare-const x (_ BitVec 8))
(pop 1)
(assert (! (= x #x2a) :named answer))
(get-assertions)
(check-sat)
(get-value (x))
(get-assignment)
(check-sat-assuming ((not answer)))
(get-unsat-assumptions)
''')
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertIn('sat\n', result.stdout)
                self.assertIn('( |x|  #x2A )', result.stdout)
                self.assertIn('(|answer| true)', result.stdout)
                self.assertIn('unsat\n', result.stdout)
                self.assertIn('(not (= |x|  #x2A))', result.stdout)

    def test_unsupported_options_after_logic_do_not_end_the_script(self):
        result = run('(set-logic QF_BV)(set-option :produce-proofs true)'
                     '(set-option :random-seed 0)(check-sat)')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, 'unsupported\nunsupported\nsat\n')

    def test_disabled_queries_are_errors(self):
        for query, option, assertion in [
                ('get-model', 'produce-models', 'true'),
                ('get-value (true)', 'produce-models', 'true'),
                ('get-assignment', 'produce-assignments', 'true'),
                ('get-proof', 'produce-proofs', 'false'),
                ('get-unsat-core', 'produce-unsat-cores', 'false'),
                ('get-unsat-assumptions', 'produce-unsat-assumptions', 'false')]:
            with self.subTest(query=query):
                self.assert_error('(set-logic QF_BV)(assert ' + assertion +
                                  ')(check-sat)(' + query + ')',
                                  query.split()[0] + ' requires :' + option + ' true')

    def test_model_queries_require_current_sat_context(self):
        for commands in ['', '(assert false)(check-sat)',
                         '(check-sat)(assert true)', '(check-sat)(push 1)',
                         '(push 1)(check-sat)(pop 1)',
                         '(check-sat)(declare-const x Bool)',
                         '(check-sat)(reset-assertions)']:
            with self.subTest(commands=commands):
                self.assert_error('(set-option :produce-models true)'
                                  '(set-logic QF_BV)' + commands + '(get-model)',
                                  'get-model is not permitted')

    def test_definitions_and_empty_stack_operations_preserve_models(self):
        for middle in ['(push 0)', '(pop 0)', '(define-sort Byte () (_ BitVec 8))',
                       '(define-fun identity ((p Bool)) Bool p)',
                       '(define-const same Bool p)']:
            with self.subTest(middle=middle):
                result = run('(set-option :produce-models true)(set-logic QF_BV)'
                             '(declare-const p Bool)(assert p)(check-sat)' +
                             middle + '(get-model)(get-value (p))')
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertIn('(define-fun |p| () Bool true)', result.stdout)
                self.assertIn('( |p| true )', result.stdout)

    def test_definitions_can_be_evaluated_in_the_existing_model(self):
        result = run('''
(set-logic QF_BV)
(set-option :produce-models true)
(declare-const x (_ BitVec 8))
(assert (= x #x2a))
(check-sat)
(define-fun next ((v (_ BitVec 8))) (_ BitVec 8) (bvadd v #x01))
(define-const y (_ BitVec 8) (next x))
(get-value (y (next x)))
''')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout.count('#x2B'), 2)

    def test_empty_stack_operations_preserve_unsat_assumptions(self):
        result = run('''
(set-option :produce-unsat-assumptions true)
(set-logic QF_BV)
(declare-const p Bool)
(check-sat-assuming (p (not p)))
(push 0)
(pop 0)
(define-fun identity ((x Bool)) Bool x)
(get-unsat-assumptions)
''')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, 'unsat\n(|p| (not |p|))\n')

    def test_definitions_preserve_real_fp_and_uf_models(self):
        cases = [
            ('QF_LRA', '(declare-const x Real)(assert (= x (/ 1 3)))',
             '(define-fun f ((v Real)) Real (+ v 1))',
             '(= (f x) (/ 4 3))'),
            ('QF_FP', '(declare-const x Float32)(assert (fp.isNaN x))',
             '(define-fun f ((v Float32)) Bool (fp.isNaN v))', '(f x)'),
            ('QF_UFBV', '(declare-const x (_ BitVec 8))'
             '(declare-fun f ((_ BitVec 8)) (_ BitVec 8))'
             '(assert (= (f x) #x2a))',
             '(define-fun g ((v (_ BitVec 8))) (_ BitVec 8) (f v))',
             '(= (g x) #x2a)')]
        for logic, declarations, definition, term in cases:
            with self.subTest(logic=logic):
                result = run('(set-option :produce-models true)(set-logic ' +
                             logic + ')' + declarations + '(check-sat)' +
                             definition + '(get-value (' + term + '))')
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertIn(' true )', result.stdout)

    def test_reset_options_and_preserve_reset_assertions_options(self):
        result = run('''
(set-option :global-declarations true)
(set-option :produce-models true)
(set-option :produce-assertions true)
(set-option :produce-unsat-assumptions true)
(set-logic QF_BV)
(declare-const p Bool)
(assert p)
(get-assertions)
(reset-assertions)
(get-option :produce-models)
(get-option :produce-assertions)
(get-option :produce-unsat-assumptions)
(get-option :global-declarations)
(check-sat-assuming (p (not p)))
(get-unsat-assumptions)
(check-sat-assuming (p))
(get-value (p))
(reset)
(get-option :produce-models)
(get-option :produce-assertions)
(get-option :produce-unsat-assumptions)
(get-option :global-declarations)
(set-logic QF_BV)
(check-sat)
''')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('true\ntrue\ntrue\ntrue\nunsat\n', result.stdout)
        self.assertIn('(not |p|)', result.stdout)
        self.assertTrue(result.stdout.endswith('false\nfalse\nfalse\nfalse\nsat\n'))

    def test_information_query_modes(self):
        for before in ['', '(check-sat)', '(assert false)(check-sat)',
                       '(check-sat)(reset-assertions)']:
            with self.subTest(before=before):
                self.assert_error('(set-logic QF_BV)' + before +
                                  '(get-info :reason-unknown)',
                                  'get-info :reason-unknown requires a preceding unknown result')

    def test_statistics_before_checks_and_after_context_changes(self):
        result = run('''
(get-info :all-statistics)
(set-logic QF_BV)
(get-info :all-statistics)
(check-sat)
(assert true)
(get-info :all-statistics)
(reset)
(get-info :all-statistics)
''')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(re.findall(r':check-sat-calls (\d+)', result.stdout),
                         ['0', '0', '1', '0'])
        # Reset must not leave the previous check's stage counters behind.
        self.assertRegex(result.stdout, r'\(:check-sat-calls 0\n'
                         r' :cpu-time [\d.]+\n :peak-memory-mb [\d.]+\)\n$')

    def test_assertions_are_always_available(self):
        for option in ['', '(set-option :produce-assertions false)',
                       '(set-option :produce-assertions true)']:
            with self.subTest(option=option):
                result = run(option + '''
(get-assertions)
(set-logic QF_BV)
(declare-const p Bool)
(assert p)
(push 1)
(assert (not p))
(get-assertions)
(pop 1)
(get-assertions)
''')
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual(result.stdout,
                                 '(\n)\n(\n|p|\n(not |p|)\n)\n(\n|p|\n)\n')


class SortAliases(unittest.TestCase):
    def test_invalid_sort_definitions_and_applications(self):
        for source, error in [
                ('(define-sort Bad () Missing)', 'unknown sort'),
                ('(define-sort Loop () Loop)', 'unknown sort'),
                ('(define-sort Id (T T) T)', 'duplicate sort parameter'),
                ('(define-sort S () Bool)(define-sort S () Bool)', 'the sort name is already defined'),
                ('(define-sort Id (T) T)(declare-const x Id)', 'wrong number of arguments'),
                ('(define-sort Id (T) T)(declare-const x (Id Bool Bool))', 'wrong number of arguments'),
                ('(push 1)(define-sort Id (T) T)(pop 1)(declare-const x (Id Bool))', 'unknown sort'),
                ('(define-sort Id (T) T)(reset-assertions)(declare-const x (Id Bool))', 'unknown sort')]:
            with self.subTest(source=source):
                result = run('(set-logic QF_BV)' + source)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(error, result.stdout)

    def test_global_parameterized_alias_survives_pop(self):
        result = run('(set-option :global-declarations true)(set-logic QF_BV)'
                     '(push 1)(define-sort Id (T) T)(pop 1)(reset-assertions)'
                     '(declare-const x (Id Bool))(assert x)(check-sat)')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, 'sat\n')


class Attributes(unittest.TestCase):
    def test_predefined_option_value_types(self):
        for source, message in [
                ('(set-option :print-success "true")', 'requires a Boolean symbol'),
                ('(set-option :produce-models)', 'requires a Boolean symbol'),
                ('(set-option :regular-output-channel stdout)', 'requires a string'),
                ('(set-option :random-seed -1)', 'requires a numeral'),
                ('(set-option :verbosity "0")', 'requires a numeral'),
                ('(set-info :status "sat")', 'requires sat, unsat, or unknown'),
                ('(set-info :status SAT)', 'requires sat, unsat, or unknown')]:
            with self.subTest(source=source):
                result = run(source)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(message, result.stdout)

    def test_metadata_does_not_resolve_term_names(self):
        result = run('(set-logic QF_BV)(declare-const x Bool)'
                     '(set-info :x x)(set-info :x (x true false Bool))'
                     '(check-sat)')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, 'sat\n')


class NamedUnsatCores(unittest.TestCase):
    prefix = '(set-option :produce-unsat-cores true)(set-logic QF_BV)'

    def check_script(self, source, args=()):
        result = run(source, args=args)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return result.stdout

    def test_projects_failed_assertions_and_preserves_assertion_occurrences(self):
        script = self.prefix + '''
(declare-const p Bool)
(declare-const q Bool)
(assert (! p :named positive))
(assert (! q :named irrelevant))
(assert (! (not p) :named negative))
(check-sat)
(get-unsat-core)
(get-unsat-core)
(get-assertions)
(check-sat)
(get-unsat-core)
'''
        for args in [(), ('--incremental=on',)]:
            with self.subTest(args=args):
                output = self.check_script(script, args)
                self.assertEqual(output.count('(|positive| |negative|)'), 3)
                self.assertNotIn('|irrelevant|', output)
                self.assertIn('(\n|p|\n|q|\n(not |p|)\n)', output)

    def test_unnamed_background_and_syntactic_labels(self):
        # All these named subterms become definitions, but none labels its
        # whole assertion. Simplification can make their ASTs identical.
        for assertion in [
                '(assert (not (! true :named nested)))',
                '(assert (let ((unused true)) (! false :named nested)))',
                '(assert (! (! false :named nested) :ignored (x (y z))))',
                '(define-fun f () Bool (! false :named nested))(assert f)',
                '(assert (and (! false :named nested) true))']:
            with self.subTest(assertion=assertion):
                output = self.check_script(self.prefix + assertion +
                                           '(check-sat)(get-unsat-core)')
                self.assertEqual(output, 'unsat\n()\n')
        output = self.check_script(self.prefix + '''
(declare-const p Bool)
(assert p)
(assert (! (not p) :named |needs background|))
(check-sat)
(get-unsat-core)
''')
        self.assertEqual(output, 'unsat\n(|needs background|)\n')
        output = self.check_script(self.prefix + '''
(assert false)
(assert (! true :named irrelevant))
(check-sat)
(get-unsat-core)
''')
        self.assertEqual(output, 'unsat\n()\n')

    def test_scopes_aliases_and_global_declarations(self):
        for global_declarations in [False, True]:
            with self.subTest(global_declarations=global_declarations):
                output = self.check_script(
                    '(set-option :global-declarations ' +
                    str(global_declarations).lower() + ')' + self.prefix + '''
(declare-const p Bool)
(assert (! p :named base))
(push 1)
(assert (! (not p) :named local))
(check-sat)
(get-unsat-core)
(pop 1)
(check-sat)
(push 1)
(assert (! (not p) :named replacement))
(check-sat)
(get-unsat-core)
(pop 1)
(assert (not base))
(check-sat)
(get-unsat-core)
''')
                self.assertEqual(output, 'unsat\n(|base| |local|)\nsat\n'
                                 'unsat\n(|base| |replacement|)\n'
                                 'unsat\n(|base|)\n')

    def test_reset_assertions_removes_labels_even_when_names_survive(self):
        output = self.check_script('(set-option :global-declarations true)' +
                                  self.prefix + '''
(assert (! false :named old))
(check-sat)
(get-unsat-core)
(reset-assertions)
(get-option :produce-unsat-cores)
(assert old)
(check-sat)
(get-unsat-core)
(reset)
(get-option :produce-unsat-cores)
''')
        self.assertEqual(output, 'unsat\n(|old|)\ntrue\nunsat\n()\nfalse\n')

    def test_unnamed_background_can_be_retracted_and_sat_models_survive(self):
        output = self.check_script('(set-option :produce-models true)' + self.prefix + '''
(declare-const p Bool)
(assert (! p :named positive))
(push 1)
(assert (not p))
(check-sat)
(get-unsat-core)
(pop 1)
(check-sat)
(get-value (p))
(check-sat-assuming ((not p)))
(get-unsat-core)
(check-sat)
(get-value (p))
''')
        self.assertEqual(output, 'unsat\n(|positive|)\nsat\n(\n( |p| true )\n)\n'
                         'unsat\n(|positive|)\nsat\n(\n( |p| true )\n)\n')

    def test_labels_quote_empty_reserved_and_spaced_names(self):
        for name in ['||', '|assert|', '|with spaces|']:
            with self.subTest(name=name):
                output = self.check_script(self.prefix +
                    '(assert (! (! false :named inner) :named ' + name +
                    '))(check-sat)(get-unsat-core)')
                self.assertEqual(output, 'unsat\n(' + name + ')\n')

    def test_core_and_assumptions_are_jointly_unsatisfiable(self):
        declarations = '(declare-const p Bool)(declare-const q Bool)(declare-const r Bool)'
        named = {'np': '(not p)', 'nq': '(not q)', 'irrelevant': 'r'}
        assertions = ''.join('(assert (! ' + term + ' :named ' + name + '))'
                             for name, term in named.items())
        for queries in ['(get-unsat-core)(get-unsat-assumptions)',
                        '(get-unsat-assumptions)(get-unsat-core)']:
            with self.subTest(queries=queries):
                output = self.check_script(self.prefix +
                    '(set-option :produce-unsat-assumptions true)' +
                    declarations + assertions + '(check-sat-assuming (p q))' + queries)
                lines = output.splitlines()
                self.assertEqual(lines[0], 'unsat')
                core, assumptions = lines[1:]
                if queries.startswith('(get-unsat-assumptions)'):
                    assumptions, core = core, assumptions
                names = re.findall(r'\|([^|]*)\|', core)
                self.assertTrue(names)
                self.assertTrue(set(names) <= {'np', 'nq'})
                # Replay exactly the two returned projections in a fresh
                # solver, without the assertions/assumptions omitted by it.
                replay = '(set-logic QF_BV)' + declarations
                replay += ''.join('(assert ' + named[name] + ')' for name in names)
                replay += '(check-sat-assuming ' + assumptions + ')'
                self.assertEqual(self.check_script(replay), 'unsat\n')

    def test_conjunctions_and_distinct_keep_valid_source_labels(self):
        for left, right in [('(and p q)', '(not q)'),
                            ('(distinct p q)', '(= p q)')]:
            with self.subTest(left=left):
                output = self.check_script(self.prefix +
                    '(declare-const p Bool)(declare-const q Bool)' +
                    '(assert (! ' + left + ' :named left))' +
                    '(assert (! ' + right + ' :named right))' +
                    '(check-sat)(get-unsat-core)')
                self.assertEqual(output, 'unsat\n(|left| |right|)\n')

    def test_cached_assumption_answer_does_not_reuse_old_occurrence_ids(self):
        output = self.check_script("""
(set-option :produce-unsat-assumptions true)
(set-logic QF_BV)
(declare-const p Bool)
(declare-const q Bool)
(declare-const r Bool)
(check-sat-assuming (r p (not p)))
(get-unsat-assumptions)
(assert false)
(check-sat)
(check-sat-assuming (q))
(get-unsat-assumptions)
""", ('--incremental=on',))
        self.assertEqual(output, 'unsat\n(|p| (not |p|))\nunsat\nunsat\n(|q|)\n')

    def test_option_changes_require_fresh_core_and_retire_permanent_units(self):
        output = self.check_script('''
(set-logic QF_BV)
(declare-const p Bool)
(assert (! p :named yes))
(assert (! (not p) :named no))
(check-sat)
(set-option :produce-unsat-cores true)
(check-sat)
(get-unsat-core)
(set-option :produce-unsat-cores false)
(check-sat)
(set-option :produce-unsat-cores true)
(check-sat)
(get-unsat-core)
''', ('--incremental=on',))
        self.assertEqual(output, 'unsat\nunsat\n(|yes| |no|)\n'
                         'unsat\nunsat\n(|yes| |no|)\n')
        result = run('(assert false)(check-sat)'
                     '(set-option :produce-unsat-cores true)(get-unsat-core)')
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('requires an unsat check', result.stdout)

    def test_stale_and_sat_cores_are_rejected(self):
        for middle in ['(assert true)', '(push 1)', '(reset-assertions)',
                       '(pop 1)(check-sat)']:
            with self.subTest(middle=middle):
                result = run(self.prefix + '(push 1)(assert (! false :named n))'
                             '(check-sat)' + middle + '(get-unsat-core)')
                self.assertNotEqual(result.returncode, 0)
                self.assertIn('get-unsat-core is not permitted', result.stdout)
        output = self.check_script(self.prefix + '(assert (! false :named n))'
            '(check-sat)(push 0)(pop 0)(define-fun f () Bool true)(get-unsat-core)')
        self.assertEqual(output, 'unsat\n(|n|)\n')

    def test_batch_and_whole_stack_routes_return_valid_cores(self):
        cases = [
            ('QF_BV', '(declare-const x (_ BitVec 8))',
             '(= x #x00)', '(= x #x01)', ('--incremental=off',)),
            ('QF_LRA', '(declare-const x Real)',
             '(> x 1)', '(< x 0)', ()),
            ('QF_UFBV', '(declare-fun f ((_ BitVec 8)) (_ BitVec 8))',
             '(= (f #x00) #x00)', '(= (f #x00) #x01)', ()),
            ('QF_ABV', '(declare-const a (Array (_ BitVec 4) (_ BitVec 4)))'
             '(declare-const b (Array (_ BitVec 4) (_ BitVec 4)))',
             '(= a b)', '(not (= a b))', ())]
        for logic, declarations, left, right, args in cases:
            with self.subTest(logic=logic):
                output = self.check_script('(set-option :produce-unsat-cores true)'
                    '(set-logic ' + logic + ')' + declarations +
                    '(assert (! ' + left + ' :named left))' +
                    '(assert (! ' + right + ' :named right))' +
                    '(check-sat)(get-unsat-core)', args)
                self.assertEqual(output, 'unsat\n(|left| |right|)\n')


class NamedTerms(unittest.TestCase):
    def test_named_definition_in_model_query_preserves_the_model(self):
        result = run('(set-option :produce-models true)'
                     '(set-option :produce-assignments true)(set-logic QF_BV)'
                     '(check-sat)(get-value ((! true :named label)))'
                     '(get-value (label))(get-assignment)')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout,
                         'sat\n(\n( true true )\n)\n(\n( true true )\n)\n'
                         '((|label| true))\n')

    def test_named_requires_a_fresh_symbol_and_closed_term(self):
        for source, message in [
                ('(assert (! true :named "label"))', ':named requires a symbol'),
                ('(assert (! true :named))', ':named requires a symbol'),
                ('(assert (! true :named true))', 'fresh, non-reserved symbol'),
                ('(assert (! true :named @label))', 'fresh, non-reserved symbol'),
                ('(declare-const label Bool)(assert (! true :named label))', 'already denotes'),
                ('(assert (! true :named label))(assert (! true :named label))', 'already denotes'),
                ('(assert (let ((p true)) (! (and p false) :named label)))', 'closed term'),
                ('(define-fun f ((p Bool)) Bool (! (or p true) :named label))', 'closed term')]:
            with self.subTest(source=source):
                result = run('(set-logic QF_BV)' + source)
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn(message, result.stdout)


class SymbolSyntax(unittest.TestCase):
    def test_strings_are_distinct_from_symbols(self):
        for source in ['(echo identifier)', '(echo |quoted identifier|)',
                       '(set-logic "QF_BV")',
                       '(set-logic QF_BV)(declare-const "x" Bool)',
                       '(set-logic QF_BV)(declare-const |true| Bool)',
                       '(set-logic QF_BV)(declare-const x (_ BitVec 08))',
                       '(set-logic QF_BV)(assert (= #b02 #b00))',
                       '(echo "complete") "unfinished']:
            with self.subTest(source=source):
                result = run(source)
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn('(error "', result.stdout)


class QualifiedIdentifiers(unittest.TestCase):
    def test_qualifier_checks_result_sort(self):
        cases = [
            '(as p (_ BitVec 1))',
            '(as true (_ BitVec 1))',
            '((as and (_ BitVec 1)) p true)',
            '(= ((as bvadd (_ BitVec 16)) x x) #x00)',
            '(= ((as (_ extract 7 4) (_ BitVec 8)) x) #x0)',
            '(= ((as (_ rotate_left 8) (_ BitVec 16)) x) #x00)',
            '(= (as (_ bv42 8) (_ BitVec 16)) #x00)',
            '(= ((as identity Bool) x) x)',
            '(= ((as f Bool) x) x)',
        ]
        for term in cases:
            with self.subTest(term=term):
                result = run('(set-logic QF_UFBV)\n'
                             '(declare-const p Bool)\n'
                             '(declare-const x (_ BitVec 8))\n'
                             '(declare-fun f ((_ BitVec 8)) (_ BitVec 8))\n'
                             '(define-fun identity ((v (_ BitVec 8))) (_ BitVec 8) v)\n'
                             '(assert ' + term + ')\n(check-sat)\n')
                self.assertNotEqual(result.returncode, 0)
                self.assertIn('qualified identifier has result sort', result.stdout)
                self.assertNotIn('sat\n', result.stdout)


class AbstractValues(unittest.TestCase):
    prefix = """
(set-option :produce-models true)
(set-logic QF_UF)
(declare-sort S 0)
(declare-sort T 0)
(declare-const x S)
(declare-fun f (S) S)
(assert (= (f x) x))
(check-sat)
(get-value (x))
"""

    def test_model_values_can_be_queried_again(self):
        result = run(self.prefix + """
(get-value ((as @S!0 S) (= x (as @S!0 S)) (f (as @S!0 S))))
(get-model)
""")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('(as |@S!0| S)', result.stdout)
        self.assertIn('true', result.stdout)
        self.assertIn('(define-fun |x| () S (as |@S!0| S))', result.stdout)
        self.assertNotIn('(declare-', result.stdout)
        self.assertNotIn('#x', result.stdout)

    def test_abstract_values_are_scoped_to_model_inspection(self):
        for suffix, message in [
            ('(assert (= x (as @S!0 S)))', 'abstract values may only occur in get-value'),
            ('(get-value ((as @S!0 T)))', 'unknown abstract value'),
            ('(get-value ((as @missing S)))', 'unknown abstract value'),
            ('(check-sat)(get-value ((as @S!0 S)))', 'unknown abstract value'),
        ]:
            with self.subTest(suffix=suffix):
                result = run(self.prefix + suffix)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(message, result.stdout)


class ArrayValues(unittest.TestCase):
    def test_array_values_replay_and_preserve_stores(self):
        source = """
(set-option :produce-models true)
(set-logic QF_ABV)
(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
(declare-const choose Bool)
(assert choose)
(assert (= a (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x11) #x01 #x22)))
(check-sat)
"""
        term = '(store (ite choose a ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x00)) #x02 #x33)'
        for queried, expected in [('a', '(store ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x11) #x01 #x22)'),
                                  (term, '(store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x11) #x01 #x22) #x02 #x33)')]:
            with self.subTest(queried=queried):
                result = run(source + '(get-value (' + queried + '))')
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertTrue(result.stdout.startswith('sat\n'))
                tokens = iter(re.findall(r'\|[^|]*\||[()]|[^\s()]+', result.stdout[4:]))

                def read(token):
                    if token != '(':
                        return token
                    values = []
                    for token in tokens:
                        if token == ')':
                            return values
                        values.append(read(token))
                    self.fail('unbalanced response')

                def render(value):
                    return '(' + ' '.join(map(render, value)) + ')' if isinstance(value, list) else value

                pairs = read(next(tokens))
                self.assertEqual(len(pairs), 1)
                self.assertEqual(len(pairs[0]), 2)
                value = render(pairs[0][1])
                replay = run('(set-logic QF_ABV)(assert (distinct ' + value + ' ' + expected + '))(check-sat)')
                self.assertEqual(replay.returncode, 0, replay.stdout + replay.stderr)
                self.assertEqual(replay.stdout, 'unsat\n')


class ErrorResponses(unittest.TestCase):
    def test_all_parse_refusals_use_regular_channel_and_stop(self):
        for source in ['(assert (let ((x true) (x false)) x))',
                       '[', '(assert (= #x00 #b0))']:
            with self.subTest(source=source), tempfile.TemporaryDirectory() as tmp:
                result = run('(set-option :regular-output-channel "responses")\n'
                             '(set-option :diagnostic-output-channel "diagnostics")\n'
                             '(set-logic QF_BV)\n' + source + '\n(echo "unreachable")', tmp)
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, '')
                self.assertEqual(result.stderr, '')
                response = (Path(tmp) / 'responses').read_text()
                self.assertEqual(response.count('(error "'), 1, response)
                self.assertNotIn('unreachable', response)


class TheoryBinders(unittest.TestCase):
    def test_reserved_words_require_quoting_as_symbols(self):
        for name in ['exists', 'forall', 'match', 'par',
                     'BINARY', 'DECIMAL', 'HEXADECIMAL', 'NUMERAL', 'STRING']:
            with self.subTest(name=name):
                result = run('(set-logic QF_BV)(declare-const ' + name +
                             ' Bool)(check-sat)')
                self.assertNotEqual(result.returncode, 0)
                self.assertIn('(error "', result.stdout)
                result = run('(set-logic QF_BV)(declare-const |' + name +
                             '| Bool)(assert |' + name + '|)(check-sat)')
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual(result.stdout, 'sat\n')

    def test_reserved_words_in_metadata_and_names(self):
        result = run('(set-info :example (lambda forall par BINARY STRING))'
                     '(set-logic QF_BV)(assert (! true :named |forall|))'
                     '(assert forall)(check-sat)')
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('(error "', result.stdout)
        result = run('(set-info :example (lambda forall par BINARY STRING))'
                     '(set-logic QF_BV)(assert (! true :named |forall|))'
                     '(assert |forall|)(check-sat)')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, 'sat\n')
        result = run('(set-logic QF_BV)(assert (! true :named forall))')
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('(error "', result.stdout)

    def test_a_let_binding_has_exactly_one_value(self):
        result = run('(set-logic QF_BV)(assert (let ((x true false)) x))(check-sat)')
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('(error "', result.stdout)

    def test_legacy_lambda_identifier(self):
        result = run('(set-logic QF_BV)(set-option :produce-models true)'
                     '(declare-const lambda Bool)(assert |lambda|)'
                     '(check-sat)(get-value (lambda))')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, 'sat\n(\n( |lambda| true )\n)\n')

    def test_binders_may_shadow_theory_symbols_locally(self):
        for source in [
                '(define-sort Id (Bool) Bool)'
                '(declare-const x (Id (_ BitVec 8)))(assert (= x #x2a))',
                '(define-sort Id (|BitVec|) BitVec)'
                '(declare-const x (Id Bool))(assert x)',
                '(define-fun f ((true Bool)) Bool true)(assert (not (f false)))',
                '(define-fun f ((and Bool)) Bool and)(assert (not (f false)))',
                '(assert (let ((|and| false)) (not and)))',
                '(assert (let ((and false)) (let ((and (not and))) and)))']:
            with self.subTest(source=source):
                result = run('(set-logic QF_BV)' + source +
                             '(declare-const p Bool)(declare-const v (_ BitVec 8))'
                             '(assert (and p true (= v #x00)))(check-sat)')
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual(result.stdout, 'sat\n')


class InlineDefinitionStorage(unittest.TestCase):
    def test_named_arguments_do_not_invalidate_surrounding_function(self):
        # Every annotation inserts a definition after the parser has looked
        # up identity; enough insertions exercise repeated table growth.
        body = 'true'
        for index in range(150):
            body = '(identity (! ' + body + ' :named n' + str(index) + '))'
        result = run('(set-logic QF_BV)(define-fun identity ((x Bool)) Bool x)'
                     '(assert ' + body + ')(check-sat)')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, 'sat\n')


if __name__ == '__main__':
    unittest.main()
