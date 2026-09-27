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
# check_cli_parity.py -- every spelling the stp binary accepts is a registry
# spelling, and every registry spelling the binary lacks is listed.
#
#   check_cli_parity.py --main tools/stp/main.cpp --tables lib/Api/tables
#
# The CLI side is read straight out of main.cpp: the string literal that
# names an option in each app.add_option / app.add_flag / bool_arg /
# int64_arg / mode_arg / fp_native_arg call, split on commas the way CLI11
# splits it ("--max-time,--max_time,-k"), with CLI11's decorations removed
# ("!--no-x" marks the negative form, "--incremental{on}" a flag value). The
# positional input file, --help/-h and --version are exempt: they are the
# frontend's own.
#
# The registry side is options.toml: every entry's name, aliases, short flag
# and negation, the [[alias]] backend flags, and the [[frontend]] rows (whose
# `cli` field spells the frontend-only registrations).
#
# Exit status 1 when a CLI spelling has no registry home, or when one CLI
# registration's spellings belong to different registry entries (an alias or
# a short flag attached to the wrong option). Registry spellings with no CLI
# form are printed and are not a failure: they are new in 3.x.

import argparse
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from generate import load_toml  # noqa: E402

REGISTRATION = re.compile(
    r'\b(?:app\.add_option|app\.add_flag|app\.set_help_flag|bool_arg|int64_arg|'
    r'mode_arg|fp_native_arg)\s*(?:<[^>]*>)?\s*\(\s*"([^"]*)"')
EXEMPT = {'file', '--help', '-h', '--version'}


def cli_registrations(main_cpp):
    """Every registration as a list of its spellings ('--name' or '-x')."""
    with open(main_cpp, encoding='utf-8') as f:
        text = f.read()
    out = []
    for m in REGISTRATION.finditer(text):
        spellings = []
        for piece in m.group(1).split(','):
            piece = piece.strip()
            if piece.startswith('!'):
                piece = piece[1:]
            piece = re.sub(r'\{[^}]*\}$', '', piece)
            if piece:
                spellings.append(piece)
        out.append(spellings)
    return out


def registry(tables_dir):
    doc = load_toml(os.path.join(tables_dir, 'options.toml'))
    long_home = {}   # '--name' -> entry name
    short_home = {}  # '-x' -> entry name
    entries = {}
    for o in doc['option']:
        name = o['name']
        entries[name] = o
        long_home['--' + name] = name
        for a in o.get('aliases', []):
            long_home['--' + a] = name
        if o.get('short'):
            short_home['-' + o['short']] = name
        if o.get('negation'):
            long_home['--' + o['negation']] = name
    for a in doc.get('alias', []):
        long_home['--' + a['name']] = a['of']
    frontend = set()
    for row in doc.get('frontend', []):
        for tok in re.findall(r'--?[A-Za-z][A-Za-z0-9.\-]*', row['cli']):
            frontend.add(tok)
    return entries, long_home, short_home, frontend


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--main', required=True)
    ap.add_argument('--tables', required=True)
    args = ap.parse_args()

    registrations = cli_registrations(args.main)
    entries, long_home, short_home, frontend = registry(args.tables)

    failures = []
    seen_cli = set()
    for spellings in registrations:
        if all(s in EXEMPT for s in spellings):
            continue
        homes = set()
        for s in spellings:
            seen_cli.add(s)
            if s in frontend:
                homes.add('<frontend>')
                continue
            home = long_home.get(s) if s.startswith('--') else short_home.get(s)
            if home is None:
                failures.append('CLI spelling %s (registration %s) is not in options.toml'
                                % (s, ','.join(spellings)))
            else:
                homes.add(home)
        if len(homes) > 1:
            failures.append('registration %s spans registry entries %s'
                            % (','.join(spellings), ', '.join(sorted(homes))))

    # the other direction: informational
    new_in_3x = []
    for spelling, name in sorted(long_home.items()):
        if spelling not in seen_cli:
            new_in_3x.append('%s (entry %s)' % (spelling, name))
    for spelling, name in sorted(short_home.items()):
        if spelling not in seen_cli:
            new_in_3x.append('%s (entry %s)' % (spelling, name))

    print('CLI registrations read from %s: %d' % (args.main, len(registrations)))
    print('registry entries: %d, CLI spellings covered: %d' % (len(entries), len(seen_cli)))
    if new_in_3x:
        print('registry spellings with no CLI form (new in 3.x, not a failure):')
        for line in new_in_3x:
            print('  ' + line)
    if failures:
        print('FAILURES:')
        for line in failures:
            print('  ' + line)
        return 1
    print('every CLI spelling has a registry home')
    return 0


if __name__ == '__main__':
    sys.exit(main())
