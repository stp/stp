#!/usr/bin/env python3
"""Command-line checks of the real stp-p executable: answers and exit codes on
every route, the options stp-p offers and those it leaves to the test driver,
refusals, input limits, deadlines, signals, a terminal stdin, the memory
guards and publication.

The group (-j greater than 1) needs a CaDiCaL with STP's clause-import
extension. On a build without it the group's cases check the refusal
instead, and everything else still runs. Arguments: stp-p, stpp-drive."""
import json
import os
import pathlib
import pty
import resource
import signal
import subprocess
import sys
import tempfile
import time

import sanitizer
binary = str(pathlib.Path(sys.argv[1]).resolve())
driver = [str(pathlib.Path(sys.argv[2]).resolve())]
sanitizer.install(binary, driver[0])
count = 0
# At most four CPUs: the label's size, and so the default -j here.
os.sched_setaffinity(0, set(sorted(os.sched_getaffinity(0))[:4]))
cpus = len(os.sched_getaffinity(0))

def run(args, source=None, expected=None, cwd=None):
    global count
    p = subprocess.run([binary, *args], input=source, text=True, capture_output=True,
                       timeout=12, cwd=cwd)
    p.stderr = sanitizer.stderr(p.stderr)
    count += 1
    if expected is not None:
        answer, code = expected
        assert (p.stdout, p.returncode) == (answer, code), (args, p.stdout, p.stderr, p.returncode)
    return p

def unhedged(data, roots, logic=''):
    """The group's report on a query that is not QF_BV: the hedge, which takes
    QF_BV only, is never forked -- the query is parsed once, by the group's
    owner -- and the roots take its CPU (when they are forked)."""
    assert data['engine'] == 'batch-group' and data['winner'] in ('owner', 'root'), data
    hedge = data['hedge']
    assert hedge['forked'] is False and (logic or 'no logic') in hedge['reason'], data
    assert data['logic'] == logic and data['fork_point'] in ('forked', 'refused', 'none'), data
    if data['fork_point'] == 'forked':
        assert data['roots'] == roots, data

sat = '(set-logic QF_BV)(declare-const x (_ BitVec 3))(assert (= x #b101))(check-sat)'
# A satisfiable query that reaches the SAT search (and so the fork point).
searched = ('(set-logic QF_BV)(declare-const x (_ BitVec 40))(declare-const y (_ BitVec 40))'
            f'(assert (= (bvmul x y) (_ bv{46337 * 46327} 40)))(assert (bvugt x (_ bv1 40)))'
            '(assert (bvugt y (_ bv1 40)))(assert (bvult x (_ bv65536 40)))'
            '(assert (bvult y (_ bv65536 40)))(check-sat)')
unsat = '(set-logic QF_BV)(declare-const x (_ BitVec 3))(assert (= x #b101))(assert (= x #b100))(check-sat)'
# Does this build run the group?
probe = subprocess.run([binary, '-j2'], input=sat, text=True, capture_output=True, timeout=30)
group = probe.returncode != 2 or 'clause-import' not in probe.stderr
if not group:
    assert not probe.stdout and 'sat.clause-exchange' in probe.stderr, probe
G = min(4, cpus)  # the widest group these checks start
J = f'-j{G}'
assert G >= 2, 'the CLI checks need two CPUs'
with tempfile.TemporaryDirectory(prefix='stpp-cli-') as tmp:
    tmp = pathlib.Path(tmp)
    for jobs in sorted({1, 2, 3, G}):
        if jobs > cpus:
            continue
        if jobs > 1 and not group:
            p = run(['-j', str(jobs)], sat)
            assert p.returncode == 2 and not p.stdout and 'clause-import' in p.stderr, p
            continue
        run(['-j', str(jobs)], sat, ('sat\n', 10))
        run(['-j', str(jobs)], unsat, ('unsat\n', 20))
    if not group:
        # -j1 and --config do not need the extension.
        run(['--config', 'eager-arrays'], sat, ('sat\n', 10))
        print(f'PASS: {count} CLI cases (no clause import in this build: the group refuses)')
        sys.exit(0)
    for form in ([J], [f'--jobs={G}'], ['--jobs', str(G)]):
        run(form, sat, ('sat\n', 10))
    for bad in ('0', '-1', '1.5', 'x', '999999999999999999999999', '4097', '00'):
        p = run(['-j', bad], sat)
        assert p.returncode == 2 and not p.stdout and p.stderr.startswith('stp-p: --jobs: '), p
    # Numbers are read in base 10: a leading zero is not octal.
    stats = tmp/'decimal.json'
    run(['-j', f'0{G}', '--stats-json', str(stats)], sat, ('sat\n', 10))
    assert json.loads(stats.read_text())['requested_jobs'] == G
    for args in (['-j', '08'], ['-j', '010'], ['--worker-memory-mib', '08']):
        p = run(args, sat)
        assert 'not in range' not in p.stderr and 'convert' not in p.stderr, (args, p)
    p = run(['-j', '010'], sat)  # ten jobs, not eight: more than the CPUs here
    assert p.returncode == 2 and 'exceed allowed CPU' in p.stderr, p
    # Without -j: the allowed CPUs, at most eight -- here the group on G.
    stats = tmp/'default.json'
    run(['--stats-json', str(stats)], searched, ('sat\n', 10))
    data = json.loads(stats.read_text())
    assert data['engine'] == 'batch-group' and data['requested_jobs'] == min(G, 8), data
    one = subprocess.run([binary, *sanitizer.flags(), '--stats-json', str(stats)], input=sat,
                         text=True, capture_output=True, timeout=12,
                         preexec_fn=lambda: os.sched_setaffinity(0, {min(os.sched_getaffinity(0))}))
    assert (one.stdout, one.returncode) == ('sat\n', 10), one
    assert json.loads(stats.read_text())['engine'] == 'ordinary', 'one CPU: -j1'
    # The test driver's ring geometry is checked with the rest of the
    # command line, naming the options.
    for args, says in ((['--exchange-ring', '63'], '--exchange-ring'),
                       (['--exchange-size', '64', '--exchange-ring', '100'], 'at least 130')):
        p = subprocess.run([*driver, J, *args], input=sat, text=True, capture_output=True,
                           timeout=12)
        assert p.returncode == 2 and not p.stdout and says in p.stderr, (args, p)
    for args in (['--bogus'], ['--timeout', 'nan'], ['--timeout', '-1'],
                 ['--worker-memory-mib', '18446744073709551615'], ['--random-seed', '-1'],
                 # measurement options and test controls are the driver's
                 ['--hedge', 'none'], ['--import-budget', '1'], ['--root0-import', 'on'],
                 [J, '--hedge', 'none'], [J, '--import-budget', '4'],
                 [J, '--root0-import', 'on'], ['-j2', '--portfolio', 'default,seed1'],
                 ['--list-configs'], [J, '--pin'], [J, '--control', 'batch-all'],
                 [J, '--clause-sharing', 'off'], [J, '--exchange-interval', '1'],
                 [J, '--import-window', '16'], [J, '--inject', 'hold-hedge'],
                 # stp-p's configurations are default and eager-arrays
                 ['--config', 'seed1'], ['--config', 'retained'],
                 ['--config', 'no-factor'], ['--config', 'fp-abstraction'],
                 [J, '--config', 'cnf-gia-high']):
        p = run(args, sat); assert p.returncode == 2 and not p.stdout, (args, p)
        assert p.stderr.startswith('stp-p: ') and p.stderr.count('stp-p: ') == 1, (args, p)
    # The options' ranges, by name, in CLI11's words.
    for args, says in ((['--timeout', 'nan'], '--timeout: must be a number of seconds'),
                       (['--random-seed', '4294967296'], '--random-seed: Value 4294967296 not in range'),
                       (['--worker-memory-mib', '18446744073709551615'], 'overflows'),
                       (['--stats-json', ''], '--stats-json: must not be empty'),
                       (['--config', 'seed1'], '--config: seed1 not in {default,eager-arrays}'),
                       ([J, '--pin'], 'not expected: --pin'), (['a', 'b'], 'not expected: b')):
        p = run(args, sat)
        assert p.returncode == 2 and not p.stdout and says in p.stderr, (args, p)
    usage = run(['--help']).stdout
    for hidden in ('--portfolio', '--hedge', '--import-budget', '--root0-import', '--pin',
                   '--list-configs'):
        assert hidden not in usage, (hidden, usage)
    assert 'root i > 0 takes N + i' in ' '.join(usage.split()), usage
    assert 'at most 8' in usage and 'copies of the loaded solver' in ' '.join(usage.split())
    assert "stp's own are 0 and 255" in usage, usage
    for name in ('with spaces.smt2', '-leading.smt2'):
        (tmp/name).write_text(sat)
        run([J, '--', name], None, ('sat\n', 10), tmp)
    run([], sat, ('sat\n', 10))
    run([J, '-'], sat, ('sat\n', 10))
    assert run(['--version']).stdout.startswith('stp-p (STP ')
    assert 'stp-p [OPTIONS] [input]' in usage, usage
    semantic = [
        '(set-logic QF_BV)(declare-const |a space| (_ BitVec 4))(define-fun add1 ((v (_ BitVec 4))) (_ BitVec 4) (bvadd v #x1))(assert (let ((v (add1 |a space|))) (= v #x0)))(check-sat)',
        '(set-logic QF_BV)(assert (= (bvudiv #b101 #b000) #b111))(assert (= (bvurem #b101 #b000) #b101))(assert (= (bvashr #b100 #b111) #b111))(assert (bvslt #b100 #b000))(check-sat)',
        '(set-logic QF_BV)(declare-const x (_ BitVec 256))(assert (= x (_ bv' + str(2**255+71) + ' 256)))(check-sat)',
        '(set-logic QF_BV)(declare-const a Bool)(assert (! a :named original))(check-sat)',
    ]
    for source in semantic:
        for j in ('1', str(G)): run(['-j', j], source, ('sat\n', 10))
    # Scripts that hide a command from a reader that ends a symbol only at
    # whitespace or a parenthesis: STP's own lexer (and SMT-LIB's) ends it at
    # a bar or a quote, and its single-query mode refuses what they hold, by
    # name, on every route, running nothing (no file is created by a hidden
    # output channel).
    channel = tmp/'hidden-channel.out'
    a0 = '(set-logic QF_BV)\n(declare-const a (_ BitVec 1))\n(assert (= a #b0))\n'
    hiding = [
        ('(set-logic QF_ABV)(declare-const m (Array (_ BitVec 4) (_ BitVec 4)))'
         '(declare-const i (_ BitVec 4))(assert (= (select m i) #x1))\n'
         '(set-info :k (x| |))(check-sat)(push 1)(assert (= (select m i) #x2))(set-info :j (| y|))\n'
         '(check-sat)\n', '(push) at line 2'),
        (a0 + '(set-info :k (x| |))(check-sat)(assert (= a #b1))(set-info :j (| y|))\n(check-sat)\n',
         '(assert) at line 4'),
        (a0 + '(set-info :k (x| |))(check-sat)(push 1)(assert (= a #b1))(set-info :j (| y|))\n(check-sat)\n',
         '(push) at line 4'),
        ('(set-logic QF_BV)\n(set-info :k (x| |))(set-option :bv-term-abstraction true)'
         '(set-info :j (| y|))\n(declare-const x (_ BitVec 8))\n(check-sat)\n',
         '(set-option :bv-term-abstraction) at line 2'),
        ('(set-logic QF_BV)\n(set-info :k (x| |))(set-option :incremental on)(set-info :j (| y|))\n'
         '(declare-const x (_ BitVec 8))\n(check-sat)\n', '(set-option :incremental) at line 2'),
        ('(set-logic QF_BV)\n(declare-const a (_ BitVec 8))\n(assert (= a #x0f))\n'
         '(set-info :k (x| |))(set-option :sat-backend minisat)(set-option :random-seed 7)'
         '(set-info :j (| y|))\n(check-sat)\n', '(set-option :sat-backend) at line 4'),
        ('(set-logic QF_BV)\n(declare-const a (_ BitVec 1))\n'
         '(set-info :k (x| |))(push 1)(assert (= a #b0))(assert (= a #b1))(check-sat)(pop 1)'
         '(set-info :j (| y|))\n(check-sat)\n', '(push) at line 3'),
        (a0 + '(set-info :k (x" "))(check-sat)(assert (= a #b1))(set-info :j (" y"))\n(check-sat)\n',
         '(assert) at line 4'),
        ('(set-logic QF_BV)\n(declare-const a (_ BitVec 1))\n(assert (= a #b0))\n(assert (= a #b1))\n'
         '(set-info :k (x| |))(check-sat)(reset-assertions)(set-info :j (| y|))\n(check-sat)\n',
         '(reset-assertions) at line 5'),
        ('(set-logic QF_BV)\n(set-info :k (x| |))(set-option :random-seed 5)(set-info :j (| y|))\n'
         '(declare-const x (_ BitVec 8))\n(check-sat)\n', '(set-option :random-seed) at line 2'),
        ('(set-logic QF_BV)\n(set-info :k (x| |))(set-option :stop-after-cnf true)(set-info :j (| y|))\n'
         '(declare-const x (_ BitVec 8))\n(check-sat)\n', '(set-option :stop-after-cnf) at line 2'),
        # The check-sat another reader sees is inside a quoted symbol, and
        # the one after it inside a comment.
        (a0 + '(set-info :k (x|))\n(check-sat)\n; |)) (assert (= a #b1))\n',
         'needs a check-sat, and the script has none'),
        (a0 + '(set-info :k (x|))\n(check-sat)\n; |)) (check-sat) (push 1) (assert (= a #b1))\n(check-sat)\n',
         '(push) at line 6'),
        (a0 + '(set-info :k (x|))\n(check-sat)\n; |)) (check-sat) (push 1) (assert (= a #b1))\n',
         '(push) at line 6'),
        ('(set-logic QF_BV)\n(declare-const a (_ BitVec 1))\n(declare-const | | (_ BitVec 1))\n'
         '(declare-const | y| (_ BitVec 1))\n(assert (= a #b0))\n'
         '(assert (bvule a| |))(check-sat)(push 1)(assert (= a #b1))(assert (bvule | y| a))\n(check-sat)\n',
         '(push) at line 6'),
        ('(set-logic QF_BV)\n(declare-const a (_ BitVec 1))\n'
         f'(set-info :k (x| |))(set-option :regular-output-channel "{channel}")'
         '(set-info :j (| y|))\n(assert (= a #b0))\n(check-sat)\n',
         '(set-option :regular-output-channel) at line 3: it would open a file'),
        ('(set-logic QF_BV)(declare-const a (_ BitVec 1))(assert (= a #b0))\n'
         '(set-info :note (p| |))\n(exit)\n(set-info :note (| q|))\n(assert (= a #b1))\n(check-sat)',
         '(exit) at line 3: it comes before the check-sat'),
    ]
    for source, names in hiding:
        for j in ('1', str(G)):
            p = run(['-j', j], source)
            assert p.returncode == 2 and not p.stdout, (source, p)
            assert 'the single-query parse mode' in p.stderr and names in p.stderr, (source, names, p)
    assert not channel.exists()
    # A backslash in a quoted symbol: STP's lexer refuses it, so the parse
    # is an error, as stp's is.
    for source in ('(set-logic QF_BV)(declare-const a (_ BitVec 1))(set-info :note |x\\ |)'
                   '(assert (= a #b1))(set-info :note | y|)(check-sat)',):
        for j in ('1', str(G)):
            p = run(['-j', j], source)
            assert p.returncode == 2 and not p.stdout, (source, p)
    # Quoted symbols and strings that hide nothing are read as written, and
    # answered as stp answers them.
    stp = pathlib.Path(binary).parent / 'stp'
    quoted = [
        ('(set-info :source |multi\nline (with parens) ; and semicolon|)\n'
         '(set-info :license "a ""|"" b (c) ; d")\n(set-logic QF_BV)\n'
         '(declare-fun |weird name| () (_ BitVec 8))(declare-fun x () (_ BitVec 8))\n'
         '(assert (= |weird name| x))(set-info :k ("a""b" |c| d x"y"|z|))\n(check-sat)\n(exit)', 'sat'),
        ('(set-logic QF_BV)(declare-const |a b| (_ BitVec 4))(declare-const |x| (_ BitVec 4))'
         '(assert (= (bvadd |a b| x) #x0))(assert (distinct |a b| #x0))(check-sat)', 'sat'),
        ('(set-logic QF_BV)(declare-const |;| Bool)(assert (and |;| (not |;|)))(check-sat)', 'unsat'),
    ]
    for source, expected in quoted:
        if stp.exists():
            ref = subprocess.run([str(stp)], input=source, text=True, capture_output=True,
                                 timeout=30)
            assert ref.stdout.split() == [expected], (source, ref)
        for j in ('1', str(G)):
            run(['-j', j], source, (expected + '\n', {'sat': 10, 'unsat': 20}[expected]))
    # set-logic once, and before any declaration or assertion, as stp takes
    # it; define-const; the two printing options, either way (ignored).
    for source, says in (
            ('(declare-const x (_ BitVec 4))(set-logic QF_BV)(check-sat)',
             '(set-logic) at line 1: it follows a declaration'),
            ('(set-logic QF_BV)(set-logic QF_BV)(declare-const a (_ BitVec 4))(check-sat)',
             '(set-logic) at line 1'),
            ('(set-logic QF_BV)(set-option :random-seed 3)(check-sat)',
             "(set-option :random-seed) at line 1: the solver's options are its caller's")):
        for j in ('1', str(G)):
            p = run(['-j', j], source)
            assert p.returncode == 2 and not p.stdout and says in p.stderr, (source, p)
    for source in ('(set-info :status sat)(set-option :print-success false)(set-logic QF_BV)'
                   '(set-option :produce-models false)(declare-const a (_ BitVec 4))'
                   '(define-const k (_ BitVec 4) #x3)(assert (= a k))(check-sat)',
                   '(set-option :produce-models true)(set-logic QF_BV)(set-option :print-success true)'
                   '(declare-const a (_ BitVec 4))(assert (= a #x3))(check-sat)'):
        for j in ('1', str(G)):
            run(['-j', j], source, ('sat\n', 10))
    # No set-logic: the content may be anything STP parses, so no hedge is
    # forked, and the roots take every CPU.
    f32 = '(_ FloatingPoint 8 24)'
    nologic = (f'(declare-const x {f32})(assert (fp.isNormal x))'
               f'(assert (fp.gt x ((_ to_fp 8 24) RNE 1.0)))(check-sat)')
    stats = tmp/'nologic.json'
    run([J, '--stats-json', str(stats)], nologic, ('sat\n', 10))
    data = json.loads(stats.read_text())
    unhedged(data, G)
    # Expected-status metadata is deliberately wrong and must have no authority.
    run([J], '(set-info :status unsat)\n; new arbitrary fixture\n'+sat, ('sat\n', 10))
    # The command shape: refused before anything is solved, on every route.
    rejected = [
        (sat+'(check-sat)', '(check-sat) at line 1: a single query has one'),
        (sat+'(assert false)', '(assert) at line 1: it follows the check-sat'),
        (sat+'(get-model)', '(get-model) at line 1: it follows the check-sat'),
        (sat+'(exit)(get-value (x))', '(get-value) at line 1: it follows the exit'),
        ('(set-logic QF_BV)(push 1)(check-sat)', '(push) at line 1'),
        ('(set-logic QF_BV)(declare-const x Bool)(check-sat-assuming (x))',
         '(check-sat-assuming) at line 1'),
        ('(set-logic QF_BV)(assert false)', 'needs a check-sat, and the script has none'),
        ('(set-logic QF_BV)(reset)(check-sat)', '(reset) at line 1'),
        ('(set-logic QF_BV)(set-logic QF_ABV)(check-sat)', '(set-logic) at line 1'),
        ('(set-logic QF_LIA)(check-sat)', 'unsupported logic'),
        ('(set-logic QF_UFBV)(check-sat)', 'logic must be QF_BV'),
        # A NUL anywhere: STP's lexer would end a quoted symbol at it.
        ('(set-logic QF_BV)(check-sat)\0', 'NUL byte at offset 28'),
        ('(set-logic QF_BV)(declare-const |a| (_ BitVec 4))(assert (= |a\0b| #x1))'
         '(assert (= |a| #x2))(check-sat)', 'NUL byte at offset 62'),
        ('(set-logic QF_BV); \0\n(check-sat)', 'NUL byte'),
    ]
    for source, says in rejected:
        for j in ('1', str(G)):
            p = run(['-j', j], source)
            assert p.returncode == 2 and not p.stdout and says in p.stderr, (source, p)
    # A parse error quotes the bytes it stopped at, which need not be UTF-8:
    # the report still goes out.
    for j in ('1', str(G)):
        p = subprocess.run([binary, '-j', j], input=b'\xef\xbb\xbf' + sat.encode(),
                           capture_output=True, timeout=12)
        assert p.returncode == 2 and not p.stdout and b'[PARSE]' in p.stderr, p
    # Sorts and operators are STP's parser's: what it refuses is an error.
    for source in ('(set-logic QF_BV)(declare-const x Int)(check-sat)',
                   '(set-logic QF_BV)(assert (= missing #b0))(check-sat)',
                   '(set-logic QF_BV)(assert (= #b00 #b0))(check-sat)'):
        for j in ('1', str(G)):
            p = run(['-j', j], source)
            assert p.returncode == 2 and not p.stdout, (source, p)
    # What STP's own parser takes is taken: a repeated exit on every logic,
    # and the SMT-LIB 2.7 overflow predicates.
    for source in (sat + '(exit)(exit)',
                   '(set-logic QF_BV)(declare-const x (_ BitVec 8))(assert (bvuaddo x x))'
                   '(assert (= x #x80))(check-sat)'):
        for j in ('1', str(G)):
            run(['-j', j], source, ('sat\n', 10))
    # Theory logics on the routes that run ordinary STP's own pipeline: -j1
    # on the ordinary route and the group (which forks no hedge for them).
    # Sorts and operators are STP's parser's to check; every other refusal
    # stands, and the strict routes still take QF_BV only.
    f32 = '(_ FloatingPoint 8 24)'
    one, two = '((_ to_fp 8 24) RNE 1.0)', '((_ to_fp 8 24) RNE 2.0)'
    theory = [
        ('QF_ABV', '(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))(declare-const i (_ BitVec 8))'
                   '(assert (= (select a i) #x01))', '(assert (= (select a i) #x02))'),
        ('QF_FP', f'(declare-const x {f32})(assert (fp.gt x {one}))(assert (fp.lt x {two}))',
                  f'(assert (fp.isNaN x))'),
        ('QF_BVFP', f'(declare-const b (_ BitVec 32))(define-fun x () {f32} ((_ to_fp 8 24) b))'
                    f'(assert (fp.eq x {one}))', '(assert (= ((_ extract 31 31) b) #b1))'),
        ('QF_ABVFP', '(declare-const m (Array (_ BitVec 32) (_ BitVec 8)))'
                     f'(define-fun x () {f32} ((_ to_fp 8 24) (concat (select m #x00000003) (concat (select m #x00000002) (concat (select m #x00000001) (select m #x00000000))))))'
                     f'(assert (fp.eq x {two}))', '(assert (= (select m #x00000003) #x00))'),
    ]
    theory_routes = (['-j1'], ['-j1', '--config', 'eager-arrays'],
                     [f'-j{G}'], [f'-j{G}', '--config', 'eager-arrays'])
    for logic, body, contra in theory:
        sat_src = f'(set-logic {logic}){body}(check-sat)'
        unsat_src = f'(set-logic {logic}){body}{contra}(check-sat)'
        for route in theory_routes:
            run(route, sat_src, ('sat\n', 10))
            run(route, unsat_src, ('unsat\n', 20))
            run(route, sat_src + '(exit)(exit)', ('sat\n', 10))
            run(route, f'(set-logic {logic})(set-option :produce-models true){body}(check-sat)',
                ('sat\n', 10))
            for bad in (sat_src + '(check-sat)', sat_src + '(get-model)',
                        sat_src + '(exit)(get-value (x))',
                        f'(set-logic {logic})(push 1){body}(check-sat)',
                        f'(set-logic {logic})(set-option :produce-unsat-cores true){body}(check-sat)',
                        f'(set-logic {logic}){body}(check-sat-assuming ())',
                        f'(set-logic {logic}){body}(check-sat)\0'):
                p = run(route, bad)
                assert p.returncode == 2 and not p.stdout, (route, bad, p)
        # No hedge on a theory logic: the roots take every CPU.
        stats = tmp/'theory-stats.json'
        run([f'-j{G}', '--stats-json', str(stats)], sat_src, ('sat\n', 10))
        unhedged(json.loads(stats.read_text()), G, logic)
    # -j2 on a theory logic: two roots, no hedge.
    stats = tmp/'theory-j2.json'
    run(['-j2', '--stats-json', str(stats)],
        f'(set-logic QF_FP)(declare-const x {f32})(assert (fp.gt x {one}))'
        f'(assert (fp.lt x {two}))(check-sat)', ('sat\n', 10))
    unhedged(json.loads(stats.read_text()), 2, 'QF_FP')
    # An unknown the library gives before the deadline is an answer, at -jN
    # as at -j1: more distinct constants of an uninterpreted sort than its
    # width tells apart (CARRIER_EXHAUSTED). Not a failed root.
    carrier = ['(declare-sort U 0)'] + [f'(declare-fun c{i} () U)' for i in range(65537)]
    carrier += ['(declare-fun x () (_ BitVec 24))(declare-fun y () (_ BitVec 24))',
                '(assert (= ((_ zero_extend 24) #xfffffd) (bvmul ((_ zero_extend 24) x) '
                '((_ zero_extend 24) y))))(assert (bvugt x #x000001))(assert (bvugt y #x000001))',
                '(assert (or (bvugt x #x000003) ' +
                ' '.join(f'(= c{i} c{(i + 1) % 65537})' for i in range(0, 65537, 2)) + '))',
                '(check-sat)']
    path = tmp/'carrier.smt2'
    path.write_text('\n'.join(carrier) + '\n')
    for j in ('1', '2'):
        stats = tmp/f'carrier{j}.json'
        p = subprocess.run([binary, '-j', j, '--timeout', '60', '--stats-json', str(stats),
                            str(path)], capture_output=True, text=True, timeout=90)
        assert (p.stdout, p.returncode) == ('unknown\n', 0), (j, p.returncode, p.stdout, p.stderr)
        data = json.loads(stats.read_text())
        assert 'uf-sort-width' in data['reason'], data
        if j == '2':
            assert data['engine'] == 'batch-group' and data['fork_point'] == 'forked', data
            assert all(c['answer'] == 'unknown' and 'uf-sort-width' in c['report']['reason']
                       for c in data['children']), data
    path.unlink()
    for route in theory_routes:
        for bad in ('(set-logic QF_UFBV)(declare-const x (_ BitVec 4))(assert (= x #x1))(check-sat)',
                    '(set-logic ALL)(declare-const x (_ BitVec 4))(assert (= x #x1))(check-sat)'):
            p = run(route, bad)
            assert p.returncode == 2 and not p.stdout, (route, bad, p)
    # Input limits: no source-size or nesting cap.
    big = tmp/'big.smt2'
    with big.open('w') as f:
        f.write('; ' + 'x' * (17 * 1024 * 1024) + '\n' + sat)
    assert big.stat().st_size > 16 * 1024 * 1024
    for j in ('1', str(G)):
        p = subprocess.run([binary, '-j', j, str(big)], capture_output=True, text=True, timeout=60)
        assert (p.stdout, p.returncode) == ('sat\n', 10), (j, p.stdout, p.stderr)
    depth = 5000
    deep = ('(set-logic QF_BV)(declare-const a Bool)(assert ' + '(not ' * depth + 'a' +
            ')' * depth + ')(check-sat)')
    for j in ('1', str(G)):
        run(['-j', j], deep, ('sat\n', 10))
    # The parse reads the source where it is, with no copy -- the owner's peak
    # during the parse holds the source once, not twice -- and then releases
    # it, as the supervisor releases its own once the owner has it. (The
    # source here is mostly a comment, cheap for STP's parser.)
    # Each is measured above what the same route holds for a tiny query, so
    # that a runtime's own memory (a sanitizer's) does not count.
    def baseline(stdin):
        stats = tmp/'baseline.json'
        p = subprocess.run([binary, '-j1', '--stats-json', str(stats),
                            *([] if stdin else [str(tmp/'baseline.smt2')])],
                           input=sat if stdin else None, capture_output=True, text=True,
                           timeout=30)
        assert (p.stdout, p.returncode) == ('sat\n', 10), p
        return json.loads(stats.read_text())
    (tmp/'baseline.smt2').write_text(sat)

    def pinned(data, base):
        source = data['source_bytes']
        over = {k: data[k] - base[k] for k in ('parse_peak_rss_bytes', 'parse_rss_bytes',
                                               'supervisor_rss_bytes')}
        assert over['parse_peak_rss_bytes'] < 1.5 * source, (over, data)
        assert over['parse_rss_bytes'] < source / 2, (over, data)
        assert over['supervisor_rss_bytes'] < source / 2, (over, data)
    large = tmp/'large.smt2'
    with large.open('w') as f:
        f.write('; ' + 'x' * (96 * 1024 * 1024) + '\n' + sat)
    stats = tmp/'large.json'
    p = subprocess.run([binary, '-j1', '--timeout', '60', '--stats-json', str(stats), str(large)],
                       capture_output=True, text=True, timeout=90)
    assert (p.stdout, p.returncode) == ('sat\n', 10), (p.returncode, p.stdout, p.stderr)
    pinned(json.loads(stats.read_text()), baseline(False))
    # A file is mapped, not read: an inherited address-space limit too small
    # for it is an error with its reason, never an abort.
    if not sanitizer.ON:
        stats = tmp/'small-as.json'
        p = subprocess.run([binary, '-j1', '--worker-memory-mib', '0', '--stats-json', str(stats),
                            str(large)], capture_output=True, text=True, timeout=90,
                           preexec_fn=lambda: resource.setrlimit(resource.RLIMIT_AS,
                                                                 (64 << 20, 64 << 20)))
        assert p.returncode in (2, 10) and p.returncode != -signal.SIGABRT, p
        assert p.returncode == 10 or ('cannot' in p.stderr or 'memory' in p.stderr.lower()), p
        assert json.loads(stats.read_text()), 'the stats are written'
    large.unlink()
    # The input is bounded by the per-process limit before anything is
    # forked: an endless stdin ends in an error within seconds, and a large
    # one within the bound still parses.
    endless = subprocess.Popen(['yes'], stdout=subprocess.PIPE)
    started = time.monotonic()
    p = subprocess.run([binary, '--worker-memory-mib', '64'], stdin=endless.stdout,
                       capture_output=True, text=True, timeout=30)
    endless.kill(); endless.wait()
    assert p.returncode == 2 and not p.stdout and 'exceeds 64 MiB' in p.stderr, p
    assert time.monotonic() - started < 10, 'an endless input was not cut short'
    stats = tmp/'stdin.json'
    p = subprocess.run([binary, '-j1', '--stats-json', str(stats)],
                       input='; ' + 'x' * (40 * 1024 * 1024) + '\n' + sat,
                       capture_output=True, text=True, timeout=60)
    assert (p.stdout, p.returncode) == ('sat\n', 10), p
    # Standard input is spooled into memory that grows in place: the owner
    # holds it once, as it holds a file, and releases it.
    pinned(json.loads(stats.read_text()), baseline(True))
    # The spool is memory, not a file: a file-size limit does not apply to
    # it (the stats file is written before the limit is set).
    p = subprocess.run(['sh', '-c', f'ulimit -f 1024; exec "$0" "$@"', binary, '-j1',
                        *sanitizer.flags()], input='; ' + 'x' * (4 * 1024 * 1024) + '\n' + sat,
                       capture_output=True, text=True, timeout=60)
    assert (p.stdout, p.returncode) == ('sat\n', 10), p
    # A closed standard input is refused at once, before the stats file
    # could take its descriptor.
    p = subprocess.run(['sh', '-c', 'exec "$0" "$@" <&-', binary, '--stats-json',
                        str(tmp/'closed.json')], capture_output=True, text=True, timeout=12)
    assert p.returncode == 2 and not p.stdout and 'standard input is closed' in p.stderr, p
    # -j2: the group has one root beside the hedge, and one root shares
    # nothing: no rings. (The hedge is held back so that the root answers.)
    stats = tmp/'j2.json'
    p = subprocess.run([*driver, '-j2', '--inject', 'hold-hedge', '--stats-json', str(stats)],
                       input=searched, capture_output=True, text=True, timeout=60)
    assert (p.stdout, p.returncode) == ('sat\n', 10), p
    r = json.loads(stats.read_text())
    assert r['roots'] == 1 and r['rings'] is None and not r['sharing'], r
    assert r['hedge']['forked'] and r['winner'] == 'root', r
    # Rings that do not fit under the per-process limit: the roots search
    # without sharing, and the stats say why -- never an error where -j1
    # answers.
    if not sanitizer.ON:
        stats = tmp/'unshared.json'
        p = subprocess.run([*driver, J, '--hedge', 'none', '--exchange-ring', str(1 << 30),
                            '--worker-memory-mib', '1024', '--stats-json', str(stats)],
                           input=searched, capture_output=True, text=True, timeout=60)
        assert (p.stdout, p.returncode) == ('sat\n', 10), p
        r = json.loads(stats.read_text())
        assert not r['sharing'] and 'clause rings' in r['sharing_off'], r
    # The memory guards: an aggregate (PSS) guard is an unknown with its
    # reason; a per-process address space too small to run is an error.
    stats = tmp/'memory.json'
    p = run(['--memory-mib', '1', '--stats-json', str(stats)], unsat)
    assert (p.stdout, p.returncode) == ('unknown\n', 0), p
    data = json.loads(stats.read_text())
    assert data['reason'] == 'aggregate sampled memory limit', data
    assert data['peak_sampled_pss_bytes'] > 1024 * 1024, data
    wide = ('(set-logic QF_BV)(declare-const x (_ BitVec 512))(declare-const y (_ BitVec 512))'
            '(assert (= (bvmul x y) (_ bv1234567 512)))(assert (bvugt x (_ bv1 512)))'
            '(assert (bvugt y (_ bv1 512)))(check-sat)')
    for j in ('1', str(G)):
        p = run(['-j', j, '--worker-memory-mib', '64'], wide)
        assert p.returncode == 2 and not p.stdout and p.stderr.strip(), (j, p)
    # Without --memory-mib nothing is sampled.
    stats = tmp/'unsampled.json'
    run(['--stats-json', str(stats)], sat, ('sat\n', 10))
    assert 'peak_sampled_rss_bytes' not in json.loads(stats.read_text())
    # The group's report on QF_BV: the hedge forked beside the roots, each
    # process reaped.
    stats = tmp/'stats.json'
    run([f'-j{G}', '--stats-json', str(stats)], searched, ('sat\n', 10))
    data = json.loads(stats.read_text())
    assert data['cleanup_complete'] and data['engine'] == 'batch-group', data
    assert data['hedge']['forked'] and data['hedge']['role'] == 'hedge', data
    if data['fork_point'] == 'forked':
        assert data['roots'] == G - 1, data
    for item in [data['hedge'], *data['children']]:
        assert not pathlib.Path('/proc', str(item['pid'])).exists(), item
    # A terminal stdin with no file is a usage error, at once.
    for args in ([], [J], ['-']):
        pid, fd = pty.fork()
        if not pid:
            os.execv(binary, [binary, *sanitizer.flags(), *args])
        output = b''
        until = time.monotonic() + 10
        status = None
        while time.monotonic() < until:
            done, status = os.waitpid(pid, os.WNOHANG)
            try:
                output += os.read(fd, 4096)
            except OSError:
                pass
            if done:
                break
            time.sleep(.01)
        else:
            os.kill(pid, signal.SIGKILL)
            os.waitpid(pid, 0)
            raise AssertionError(('a terminal stdin hung', args, output))
        os.close(fd)
        assert os.WIFEXITED(status) and os.WEXITSTATUS(status) == 2, (args, status, output)
        assert b'terminal' in output and b'sat' not in output, (args, output)
    # Blocked input is covered by the native wall deadline; keep the pipe open.
    p = subprocess.Popen([binary, '--timeout', '.1'], stdin=subprocess.PIPE,
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    p.wait(timeout=3)
    assert p.stdout.read() == 'unknown\n' and p.returncode == 0
    p.stdin.close()
    # Parent-directed signals clean a blocked input owner without publishing SAT.
    for sig in (signal.SIGINT, signal.SIGTERM):
        p = subprocess.Popen([binary], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        time.sleep(.03); p.send_signal(sig); p.wait(timeout=3)
        assert p.returncode == 128+sig and not p.stdout.read()
        p.stdin.close()
    # A stats file that cannot be opened is a usage error, before anything
    # runs; one whose write fails at the end costs the stats, never the
    # answer.
    p = run(['--stats-json', str(tmp/'absent'/'stats.json')], sat)
    assert p.returncode == 2 and not p.stdout
    small = tmp/'small.smt2'
    small.write_text(sat)
    def tiny_files():
        resource.setrlimit(resource.RLIMIT_FSIZE, (16, 16))
        signal.signal(signal.SIGXFSZ, signal.SIG_IGN)
    p = subprocess.run([binary, '--stats-json', str(tmp/'late.json'), str(small)],
                       capture_output=True, text=True, timeout=12, preexec_fn=tiny_files)
    assert (p.stdout, p.returncode) == ('sat\n', 10) and 'not written' in p.stderr, p
    # An answer in hand when the deadline stops the run is published: the
    # owner (a driver fault) lingers after its report.
    p = subprocess.run([*driver, '-j1', '--inject', 'linger', '--timeout', '2', str(small)],
                       capture_output=True, text=True, timeout=20)
    assert (p.stdout, p.returncode) == ('sat\n', 10), p
    # The supervisor compares what the owner passed on with its report: a
    # contradiction there (a driver fault) is an error with the evidence, and
    # so it is when the deadline stops a lingering owner after both arrived.
    for extra in ([], ['--inject', 'contradict,linger', '--timeout', '1']):
        stats = tmp/'contradict.json'
        p = subprocess.run([*driver, '-j1', *(extra or ['--inject', 'contradict']),
                            '--stats-json', str(stats), str(small)],
                           capture_output=True, text=True, timeout=20)
        assert p.returncode == 2 and not p.stdout and 'complete answers disagree' in p.stderr, p
        data = json.loads(stats.read_text())
        assert data['fatal'] and data['evidence']['records'][0]['answer'] == 'unsat', data
        assert data['evidence']['report']['answer'] == 'sat', data
    # A report the deadline cut short is no report: the run is unknown, with
    # the stop's reason, never a malformed report.
    stats = tmp/'cut.json'
    p = subprocess.run([*driver, '-j1', '--inject', 'cut-report', '--timeout', '1',
                        '--stats-json', str(stats), str(small)],
                       capture_output=True, text=True, timeout=20)
    assert (p.stdout, p.returncode) == ('unknown\n', 0), p
    data = json.loads(stats.read_text())
    assert data['owner_report_cut'] and data['reason'] == 'wall timeout', data
    # An answer that standard output cannot take is still the exit status;
    # stderr says the line was lost.
    readfd, writefd = os.pipe2(os.O_NONBLOCK)
    try:
        while True:
            os.write(writefd, b'x' * 4096)
    except BlockingIOError:
        pass
    p = subprocess.run([binary, '-j1', '--timeout', '.5', str(small)], stdout=writefd,
                       stderr=subprocess.PIPE, text=True, timeout=12)
    os.close(readfd)
    os.close(writefd)
    assert p.returncode == 10 and 'answer line (sat) was lost' in p.stderr, p
    # The deadline itself: unknown, and the stats say the deadline stopped
    # the run -- nothing was published late.
    stats = tmp/'deadline.json'
    hard = searched.replace(str(46337 * 46327), str(2147483647))  # a prime: unsat, slowly
    p = run(['--timeout', '.5', '--stats-json', str(stats)], hard)
    data = json.loads(stats.read_text())
    if p.stdout == 'unknown\n':
        assert data.get('stopped_by', data.get('reason')) in ('wall timeout',) or \
            'timeout' in data.get('reason', ''), data
        assert 'before publication' not in json.dumps(data), data
    tmp.chmod(0o555)
    run([J], sat, ('sat\n', 10), tmp)
    tmp.chmod(0o755)
print(f'PASS: {count} CLI cases plus blocked-input and signal cleanup')
