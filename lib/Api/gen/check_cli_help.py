#!/usr/bin/env python3
#********************************************************************
# AUTHORS: Andrew Teylu
#
# BEGIN DATE: September, 2026
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
# THE SOFTWARE.
#********************************************************************
#
# check_cli_help.py -- the stp binary's command line is the option registry.
#
#   check_cli_help.py --stp build/stp --tables lib/Api/tables
#
# tools/stp/main.cpp registers its options from options.toml, so what this
# checks is the result rather than the source: `stp --help` names every entry
# with a CLI form (with its aliases, short flag and negation), every [[alias]]
# backend flag this build has, and every [[frontend]] row; each group of the
# [[cli_group]] section is printed; and a sample of spellings parses -- one
# value-taking entry per type, an alias, a negation and a short flag -- with
# the answer of a one-line query unchanged.
#
# Entries with a build requirement are listed only when the binary reports
# that backend in --version (a build without CaDiCaL hides the CaDiCaL rows),
# so the check reads --version first.

import argparse
import os
import re
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from generate import load_toml  # noqa: E402

QUERY = '(set-logic QF_BV)\n(declare-fun x () (_ BitVec 8))\n(assert (= x #x01))\n(check-sat)\n(exit)\n'


def run(args, stdin=None):
    return subprocess.run(args, input=stdin, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--stp', required=True)
    ap.add_argument('--tables', required=True)
    args = ap.parse_args()
    doc = load_toml(os.path.join(args.tables, 'options.toml'))

    # --version prints "STP SAT solvers <name> <version>, ...": which backends
    # this build has, and so which rows and flags --help must list.
    version = run([args.stp, '--version']).stdout.lower()
    solvers = ''
    for line in version.splitlines():
        if line.startswith('stp sat solvers'):
            solvers = line
    have = {
        'cadical': 'cadical' in solvers,
        'cryptominisat': 'cryptominisat' in solvers,
        'minisat': 'minisat' in solvers.replace('cryptominisat', ''),
    }

    help_out = run([args.stp, '--help']).stdout
    failures = []

    def expect(text, why):
        if text not in help_out:
            failures.append('%s: %r is not in --help' % (why, text))

    for g in doc.get('cli_group', []):
        expect(g['name'] + ':', 'group')

    for o in doc['option']:
        if o.get('cli_form', 'value') == 'none':
            continue
        build = o.get('requires', {}).get('build')
        if build in have and not have[build]:
            continue
        if build in ('highs', 'highs-cut-log'):
            continue  # hidden unless the build has HiGHS, which --version does not say
        expect('--' + o['name'], 'entry ' + o['name'])
        for a in o.get('aliases', []):
            expect('--' + a, 'alias of ' + o['name'])
        if o.get('short'):
            expect('-' + o['short'] + ',', 'short flag of ' + o['name'])
        if o.get('negation') and o.get('cli_form') == 'flag':
            expect('--' + o['negation'], 'negation of ' + o['name'])
        # the first sentence of the help text (CLI11 wraps long texts)
        first = re.split(r'[.;:]', o['help'])[0][:40].strip()
        if first:
            expect(first, 'help of ' + o['name'])

    for a in doc.get('alias', []):
        if have.get(a['value'].replace('simplifying-', ''), True):
            expect('--' + a['name'], 'backend flag')
    for r in doc.get('frontend', []):
        if r['kind'] == 'positional':
            continue
        expect(r['cli'].split(',')[0], 'frontend ' + r['key'])

    # a sample of spellings parses and leaves a trivial query's answer alone
    with tempfile.NamedTemporaryFile('w', suffix='.smt2', delete=False) as f:
        f.write(QUERY)
        path = f.name
    try:
        samples = [
            ['--flattening=true'], ['--flattening', 'false'], ['--aig-rewrite-passes=1'],
            ['--uf-sort-width', '8'], ['--lra-relu-bounds=auto'], ['--search-bias=unsat'],
            ['--bv-term-abstraction-schema-groups=base,urem'], ['--max-time', '5'], ['--max_time=500ms'],
            ['-k', '2'], ['--switch-word'], ['-w'], ['--no-incremental-promote-units'],
            ['--incremental'], ['--incremental=off'], ['--array-equality'], ['--stop-after-cnf'],
            ['--sat-backend=auto'], ['--produce-models=false'], ['--simplify=false'],
        ]
        for value, flag in (('cadical', '--cadical'), ('cryptominisat', '--cryptominisat')):
            if have.get(value):
                samples.append([flag])
        for s in samples:
            r = run([args.stp] + s + [path])
            if r.returncode != 0 or 'sat' not in r.stdout.split():
                failures.append('%s: exit %d, stdout %r, stderr %r' % (' '.join(s), r.returncode, r.stdout, r.stderr))
        # and a refused value is a usage error on stderr, not a crash
        r = run([args.stp, '--search-bias=bogus', path])
        if r.returncode == 0 or 'must be one of' not in r.stderr or r.stdout.strip():
            failures.append('--search-bias=bogus: exit %d, stdout %r, stderr %r' % (r.returncode, r.stdout, r.stderr))
    finally:
        os.unlink(path)

    print('--help: %d lines; %d entries checked' % (len(help_out.splitlines()), len(doc['option'])))
    if failures:
        print('FAILURES:')
        for line in failures:
            print('  ' + line)
        return 1
    print('every registry spelling is on the command line')
    return 0


if __name__ == '__main__':
    sys.exit(main())
