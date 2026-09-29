"""SMT-LIB command protocol checks that need separate channels or files."""

from pathlib import Path
import re
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
                     '(set-option :produce-unsat-cores true)'
                     '(set-option :random-seed 0)(check-sat)')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, 'unsupported\nunsupported\nunsupported\nsat\n')

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
        for name in ['lambda', 'exists', 'forall', 'match', 'par',
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
                     '(set-logic QF_BV)(assert (! true :named |lambda|))'
                     '(assert lambda)(check-sat)')
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('(error "', result.stdout)
        result = run('(set-info :example (lambda forall par BINARY STRING))'
                     '(set-logic QF_BV)(assert (! true :named |lambda|))'
                     '(assert |lambda|)(check-sat)')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, 'sat\n')
        result = run('(set-logic QF_BV)(assert (! true :named lambda))')
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('(error "', result.stdout)

    def test_a_let_binding_has_exactly_one_value(self):
        result = run('(set-logic QF_BV)(assert (let ((x true false)) x))(check-sat)')
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('(error "', result.stdout)

    def test_binders_cannot_shadow_theory_symbols(self):
        for command in ['(define-sort Bad (Bool) Bool)',
                        '(define-sort Bad (|BitVec|) BitVec)',
                        '(define-fun bad ((true Bool)) Bool true)',
                        '(assert (let ((|and| false)) and))']:
            with self.subTest(command=command):
                result = run('(set-logic QF_BV)' + command + '(check-sat)')
                self.assertNotEqual(result.returncode, 0)
                self.assertIn('cannot shadow theory', result.stdout)


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
