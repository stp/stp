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
# generate.py -- the STP 3.x table generator.
#
# Reads the four tables in lib/Api/tables (kinds.toml, options.toml, errors.toml,
# statistics.toml) and writes every generated fragment of the public API: the C++
# and C enums, the named term constructors in both languages, the registry rows the
# implementation walks, and the Cython enum declarations. The tables are the single
# source; nothing here is edited by hand.
#
#   generate.py --tables DIR --out DIR [--check] [--toml-subset]
#   generate.py --tables DIR --out DIR --self-test
#
# Outputs (relative to --out):
#   include/stp/api/gen/kinds.hpp        enum class Kind, to_string tables are in kind_table.inc
#   include/stp/api/gen/kind_ctors.hpp   the named C++ constructors and literal overloads
#   include/stp/api/gen/options.hpp      enum class Option (the stable tier)
#   include/stp/api/gen/errors.hpp       enum class ErrorCode
#   include/stp/api/gen/kinds.h          enum stp_kind
#   include/stp/api/gen/kind_ctors.h     the named C constructors (non-indexed kinds)
#   include/stp/api/gen/options.h        enum stp_option
#   include/stp/api/gen/errors.h         enum stp_error_code
#   lib/Api/gen/kind_table.inc           KindSpec rows
#   lib/Api/gen/kind_ctors.inc           the named C++ constructor definitions
#   lib/Api/gen/kind_ctors_c.inc         the named C constructor definitions
#   lib/Api/gen/option_table.inc         OptionSpec rows
#   lib/Api/gen/option_apply.inc         the option -> engine apply switch
#   lib/Api/gen/option_defaults.inc      the engine default of every field-mapped option, for the parity test
#   lib/Api/gen/cli_table.inc            the --help groups, the backend-flag aliases and the frontend rows of tools/stp
#   lib/Api/gen/error_table.inc          ErrorSpec rows
#   lib/Api/gen/stat_table.inc           StatSpec rows
#   python/_gen_enums.pxi                Cython enum declarations
#   python/_gen_kinds.py                 the Python Kind/Option/ErrorCode enums
#
# Python 3.8+; uses tomllib when the interpreter has it (3.11+) and otherwise the
# small TOML subset parser below, which covers exactly what the tables use.

import argparse
import os
import re
import sys

try:
    import tomllib  # Python 3.11+
except ImportError:  # pragma: no cover - older interpreters use the subset parser
    tomllib = None


# --------------------------------------------------------------------------- TOML subset

def _parse_value(text):
    text = text.strip()
    if text.startswith('"'):
        out = []
        i = 1
        while i < len(text):
            c = text[i]
            if c == '\\':
                nxt = text[i + 1]
                out.append({'n': '\n', 't': '\t', '"': '"', '\\': '\\'}[nxt])
                i += 2
                continue
            if c == '"':
                return ''.join(out), text[i + 1:].strip()
            out.append(c)
            i += 1
        raise ValueError('unterminated string: ' + text)
    if text.startswith('['):
        items = []
        rest = text[1:].strip()
        while not rest.startswith(']'):
            value, rest = _parse_value(rest)
            items.append(value)
            rest = rest.strip()
            if rest.startswith(','):
                rest = rest[1:].strip()
        return items, rest[1:].strip()
    if text.startswith('{'):
        table = {}
        rest = text[1:].strip()
        while not rest.startswith('}'):
            key, rest = _parse_key(rest)
            value, rest = _parse_value(rest)
            table[key] = value
            rest = rest.strip()
            if rest.startswith(','):
                rest = rest[1:].strip()
        return table, rest[1:].strip()
    m = re.match(r'(true|false|-?\d+)', text)
    if not m:
        raise ValueError('cannot parse value: ' + text)
    token = m.group(1)
    rest = text[m.end():].strip()
    if token == 'true':
        return True, rest
    if token == 'false':
        return False, rest
    return int(token), rest


def _parse_key(text):
    """A key and its '=': bare (letters, digits, - and _) or quoted, the
    quotes not part of the key, as TOML reads it. Returns (key, the text
    after the '=')."""
    text = text.strip()
    if text.startswith('"'):
        key, rest = _parse_value(text)
    else:
        m = re.match(r'[A-Za-z0-9_-]+', text)
        if not m:
            raise ValueError('cannot parse key: ' + text)
        key, rest = m.group(0), text[m.end():]
    rest = rest.strip()
    if not rest.startswith('='):
        raise ValueError('expected = after key %r: %s' % (key, text))
    return key, rest[1:]


def _strip_comment(line):
    out = []
    in_string = False
    i = 0
    while i < len(line):
        c = line[i]
        if c == '"' and (i == 0 or line[i - 1] != '\\'):
            in_string = not in_string
        if c == '#' and not in_string:
            break
        out.append(c)
        i += 1
    return ''.join(out)


def _mini_toml(text):
    root = {}
    current = root
    for raw in text.splitlines():
        line = _strip_comment(raw).strip()
        if not line:
            continue
        if line.startswith('[['):
            name = line[2:line.index(']]')].strip()
            current = {}
            root.setdefault(name, []).append(current)
            continue
        if line.startswith('['):
            name = line[1:line.index(']')].strip()
            current = root.setdefault(name, {})
            continue
        key, value = _parse_key(line)
        parsed, rest = _parse_value(value)
        if rest:
            raise ValueError('trailing text after value: ' + raw)
        current[key] = parsed
    return root


def load_toml(path, subset=False):
    """The table at `path`: through tomllib when the interpreter has it,
    unless `subset` asks for the subset parser that older ones use."""
    with open(path, 'rb') as f:
        data = f.read()
    if tomllib is not None and not subset:
        return tomllib.loads(data.decode('utf-8'))
    return _mini_toml(data.decode('utf-8'))


# --------------------------------------------------------------------------- helpers

def cstr(s):
    if s is None:
        return 'nullptr'
    return '"' + str(s).replace('\\', '\\\\').replace('"', '\\"').replace('\n', '\\n') + '"'


def c_i64(v):
    """A std::int64_t initializer that every compiler reads as written. MSVC
    types an unsuffixed 2147483648 as unsigned long, so -2147483648 would be
    +2147483648 there; the suffix makes every literal a long long."""
    v = int(v)
    if v == -2 ** 63:
        return '(-9223372036854775807LL - 1)'
    return '%dLL' % v


def c_name(cpp):
    """The C spelling of a C++ named constructor: stp_ + name minus a trailing underscore."""
    return 'stp_' + cpp.rstrip('_')


def arity_bounds(arity):
    if arity.startswith('n>='):
        return int(arity[3:]), -1
    n = int(arity)
    return n, n


def parse_sig(sig):
    """'(RM, FP[e,s], FP[e,s]) -> FP[e,s]' -> (['RM', 'FP', 'FP'], 'FP')."""
    m = re.match(r'\((.*?)\)\s*->\s*(\S+)', sig)
    # split on the commas outside brackets: "FP[e,s]" is one operand
    operands, depth, cur = [], 0, ''
    for ch in m.group(1):
        if ch == '[':
            depth += 1
        elif ch == ']':
            depth -= 1
        if ch == ',' and depth == 0:
            operands.append(cur.strip())
            cur = ''
        else:
            cur += ch
    if cur.strip():
        operands.append(cur.strip())
    operands = [o for o in operands if o and o != '...']
    def base(tok):
        tok = tok.split('[')[0]
        return tok
    return [base(o) for o in operands], base(m.group(2))


HEADER = '// Generated by lib/Api/gen/generate.py from lib/Api/tables -- do not edit.\n'


def _pinned_ids(rows, what):
    """The rows in the order of their pinned `id`s, which must be 0..n-1, each once."""
    ids = [r.get('id') for r in rows]
    if any(not isinstance(i, int) or isinstance(i, bool) for i in ids):
        raise SystemExit('%s: every entry needs an integer id' % what)
    if sorted(ids) != list(range(len(rows))):
        dup = sorted(set(i for i in ids if ids.count(i) > 1))
        raise SystemExit('%s: ids must be 0 to %d, each once (duplicated: %s; missing: %s)'
                         % (what, len(rows) - 1, dup, sorted(set(range(len(rows))) - set(ids))))
    return sorted(rows, key=lambda r: r['id'])


class Emitter:
    def __init__(self, tables, out, check):
        # Kinds in the order of their pinned ids, which are the enum values;
        # moving a row in the file changes nothing.
        self.kinds = _pinned_ids(tables['kinds']['kind'], 'kinds.toml')
        self.options = tables['options']['option']
        self.cli_groups = tables['options'].get('cli_group', [])
        self.categories = tables['options'].get('category', [])
        self.aliases = tables['options'].get('alias', [])
        self.frontend = tables['options'].get('frontend', [])
        self.errors = tables['errors']['error']
        self.stats = tables['statistics']['stat']
        self.out = out
        self.check = check
        self.changed = []
        self.validate()

    def validate(self):
        names = [k['name'] for k in self.kinds]
        if len(names) != len(set(names)):
            raise SystemExit('kinds.toml: duplicate kind name')
        onames = [o['name'] for o in self.options]
        if len(onames) != len(set(onames)):
            dup = [n for n in onames if onames.count(n) > 1]
            raise SystemExit('options.toml: duplicate option name %s' % dup)
        for o in self.options:
            for alias in o.get('aliases', []):
                if alias in onames:
                    raise SystemExit('options.toml: alias %s of %s is also a name' % (alias, o['name']))
            if o['type'] in ('enum', 'set') and 'values' not in o:
                raise SystemExit('options.toml: %s has no values' % o['name'])
            if o['type'] == 'enum' and o['default'] != '' and o['default'] not in o['values']:
                raise SystemExit('options.toml: %s: default %r is not one of its values' % (o['name'], o['default']))
            if o['type'] == 'mode' and 'values' in o:
                if not set(o['values']) <= {'on', 'off', 'auto'} or o['default'] not in o['values']:
                    raise SystemExit('options.toml: %s: a mode lists spellings among on, off and auto, its default included' % o['name'])
            if o['type'] in ('int', 'uint') and 'values' in o and str(o['default']) not in o['values']:
                raise SystemExit('options.toml: %s: default %r is not one of its values' % (o['name'], o['default']))
            if o['type'] == 'set' and any(m not in o['values'] for m in o['default']):
                raise SystemExit('options.toml: %s: default %r has a member outside its values' % (o['name'], o['default']))
            for ex in o.get('excludes', []):
                if ex not in onames:
                    raise SystemExit('options.toml: %s excludes unknown %s' % (o['name'], ex))
            if 'follows' in o and o['follows'] not in onames:
                raise SystemExit('options.toml: %s follows unknown %s' % (o['name'], o['follows']))
            # the entries the implications name are looked up by name at run
            # time, where a misspelt one would silently imply nothing
            implies = o.get('implies', {})
            for other in (implies if isinstance(implies, dict) else {}):
                if other not in onames:
                    raise SystemExit('options.toml: %s implies unknown %s' % (o['name'], other))
            for other in o.get('implied_by', {}):
                if other not in onames:
                    raise SystemExit('options.toml: %s is implied by unknown %s' % (o['name'], other))
            required = o.get('requires', {}).get('option')
            if required is not None and required not in onames:
                raise SystemExit('options.toml: %s requires unknown %s' % (o['name'], required))
            if 'id' in o and o['tier'] != 'stable':
                raise SystemExit('options.toml: %s: only a stable entry has an id' % o['name'])
            if ('cli_help' in o or 'cli_default' in o) and o.get('cli_form', 'value') == 'none':
                raise SystemExit('options.toml: %s: cli_help and cli_default are for an entry the command line has' % o['name'])
            latch = o.get('latched_by')
            if latch is not None:
                other = next((p for p in self.options if p['name'] == latch), None)
                if other is None or other['type'] != 'bool' or o['settable'] != 'anytime':
                    raise SystemExit('options.toml: %s: latched_by names a bool entry, on an anytime entry' % o['name'])
            form = o.get('cli_form', 'value')
            if form not in ('value', 'flag', 'none'):
                raise SystemExit('options.toml: %s: cli_form %r is not value, flag or none' % (o['name'], form))
            if form == 'flag' and o['type'] not in ('bool', 'mode'):
                raise SystemExit('options.toml: %s: only a bool or mode entry can be a CLI flag' % o['name'])
            tmpl = o.get('cli_bad_value')
            if tmpl is not None:
                holes = set(re.findall(r'\{([a-z]+)\}', tmpl))
                if not holes <= {'name', 'value', 'member', 'expected'}:
                    raise SystemExit('options.toml: %s: cli_bad_value may use {name}, {value}, {member} and {expected} only' % o['name'])
            for key in ('cli_below_min', 'cli_above_max'):
                if key in o:
                    side = 'min' if key == 'cli_below_min' else 'max'
                    if o['type'] not in ('int', 'uint') or side not in o.get('range', {}):
                        raise SystemExit('options.toml: %s: %s needs an int or uint entry with a range %s' % (o['name'], key, side))
                    if not set(re.findall(r'\{([a-z]+)\}', o[key])) <= {'name'}:
                        raise SystemExit('options.toml: %s: %s may use {name} only' % (o['name'], key))
            if 'cli_take_last' in o and not isinstance(o['cli_take_last'], bool):
                raise SystemExit('options.toml: %s: cli_take_last is true or false' % o['name'])
            if 'cli_empty' in o and (o['cli_empty'] != 'unset' or o['type'] not in ('set', 'enum', 'string')):
                raise SystemExit('options.toml: %s: cli_empty is "unset", on a set, enum or string entry' % o['name'])
            cr = o.get('cli_range')
            if cr is not None:
                if o['type'] not in ('int', 'uint') or 'min' not in cr or 'max' not in cr or cr['min'] > cr['max']:
                    raise SystemExit('options.toml: %s: cli_range needs min <= max on an int or uint entry' % o['name'])
        self.stable_options()  # refuses duplicate or missing ids
        self.validate_cli()
        values = [e['value'] for e in self.errors]
        if len(values) != len(set(values)):
            raise SystemExit('errors.toml: duplicate value')

    def cli_spellings(self):
        """Every spelling the CLI accepts: option names, aliases, negations, short flags, the
        [[alias]] flags and the [[frontend]] rows."""
        out = set()
        for o in self.options:
            if o.get('cli_form', 'value') == 'none':
                continue
            out.add('--' + o['name'])
            for a in o.get('aliases', []):
                out.add('--' + a)
            if o.get('negation'):
                out.add('--' + o['negation'])
            if o.get('short'):
                out.add('-' + o['short'])
        for a in self.aliases:
            out.add('--' + a['name'])
        for row in self.frontend:
            for sp in row['cli'].split(','):
                out.add(sp.strip())
        return out

    def validate_cli(self):
        """The [[cli_group]], [[category]], [[alias]] and [[frontend]] sections agree with the entries."""
        onames = {o['name']: o for o in self.options}
        groups = [g['name'] for g in self.cli_groups]
        if len(groups) != len(set(groups)):
            raise SystemExit('options.toml: duplicate cli_group')
        cats = {c['name']: c for c in self.categories}
        for c in self.categories:
            if c['group'] not in groups:
                raise SystemExit('options.toml: category %s names unknown group %s' % (c['name'], c['group']))
        for o in self.options:
            if o['category'] not in cats:
                raise SystemExit('options.toml: %s: category %s has no [[category]] row' % (o['name'], o['category']))
        for a in self.aliases:
            of = onames.get(a['of'])
            if of is None:
                raise SystemExit('options.toml: alias %s of unknown entry %s' % (a['name'], a['of']))
            if of['type'] != 'enum' or a['value'] not in of['values']:
                raise SystemExit('options.toml: alias %s: %r is not a value of %s' % (a['name'], a['value'], a['of']))
            if a['name'] in onames:
                raise SystemExit('options.toml: alias %s is also an entry name' % a['name'])
            if 'help' not in a:
                raise SystemExit('options.toml: alias %s has no help' % a['name'])
        keys = [r['key'] for r in self.frontend]
        if len(keys) != len(set(keys)):
            raise SystemExit('options.toml: duplicate frontend key')
        spellings = self.cli_spellings()
        for r in self.frontend:
            if r['kind'] not in ('positional', 'help', 'flag', 'bool-option'):
                raise SystemExit('options.toml: frontend %s: unknown kind %s' % (r['key'], r['kind']))
            if r['kind'] != 'positional' and r.get('group') not in groups:
                raise SystemExit('options.toml: frontend %s names unknown group %r' % (r['key'], r.get('group')))
            for ex in r.get('excludes', []):
                if ex not in spellings:
                    raise SystemExit('options.toml: frontend %s excludes unknown spelling %s' % (r['key'], ex))

    def write(self, rel, text):
        path = os.path.join(self.out, rel)
        os.makedirs(os.path.dirname(path), exist_ok=True)
        old = None
        if os.path.exists(path):
            with open(path, 'r', encoding='utf-8') as f:
                old = f.read()
        if old == text:
            return
        self.changed.append(rel)
        if self.check:
            return
        with open(path, 'w', encoding='utf-8') as f:
            f.write(text)

    # ----------------------------------------------------------------- kinds

    def stable_options(self):
        """The stable tier in the order of the pinned ids, the Option enum's values."""
        return _pinned_ids([o for o in self.options if o['tier'] == 'stable'], 'options.toml (stable tier)')

    def emit_kinds_hpp(self):
        lines = [HEADER, '#ifndef STP_API_GEN_KINDS_HPP', '#define STP_API_GEN_KINDS_HPP', '',
                 '#include <cstdint>', '', 'namespace stp {', 'namespace api {', '',
                 '/// Term kinds: one entry per public operator (kinds.toml), each value pinned by its id.',
                 'enum class Kind : std::uint16_t {']
        for k in self.kinds:
            lines.append('  %s = %d,  ///< %s' % (k['name'], k['id'], k['sig']))
        lines.append('  NUM_KINDS = %d' % len(self.kinds))
        lines.append('};')
        lines += ['', '}  // namespace api', '}  // namespace stp', '', '#endif', '']
        self.write('include/stp/api/gen/kinds.hpp', '\n'.join(lines))

    def emit_kinds_h(self):
        lines = [HEADER, '#ifndef STP_API_GEN_KINDS_H', '#define STP_API_GEN_KINDS_H', '',
                 'typedef enum stp_kind {']
        for k in self.kinds:
            lines.append('  STP_KIND_%s = %d,' % (k['name'], k['id']))
        lines.append('  STP_NUM_KINDS = %d,' % len(self.kinds))
        lines.append('  STP_KIND_MAX_ENUM = 0x7fffffff /* not a kind: widens the enum to int (stp.h) */')
        lines.append('} stp_kind;')
        lines += ['', '#endif', '']
        self.write('include/stp/api/gen/kinds.h', '\n'.join(lines))

    def emit_kind_table(self):
        lines = [HEADER, '// KindSpec rows, indexed by Kind.']
        for k in self.kinds:
            lo, hi = arity_bounds(k['arity'])
            operands, result = parse_sig(k['sig'])
            lines.append('  { Kind::%s, %s, %s, %s, %d, %d, %d, %s, %s, %s },' % (
                k['name'], cstr(k['name']), cstr(k['smtlib']), cstr(k['c']) if k['c'] else cstr(''),
                lo, hi, k['indices'], cstr(k['sig']), cstr(k.get('engine', '')),
                cstr(k.get('py', ''))))
        self.write('lib/Api/gen/kind_table.inc', '\n'.join(lines) + '\n')

    # The literal-overload classes of a named constructor, derived from its signature.
    def literal_class(self, k):
        operands, result = parse_sig(k['sig'])
        rm_first = bool(operands) and operands[0] == 'RM'
        rest = operands[1:] if rm_first else operands
        if k['indices'] != 0 or k['name'] in ('APPLY', 'ITE', 'SELECT', 'STORE', 'CONST_ARRAY',
                                              'FP_FP', 'IMPLIES', 'BV_CONCAT'):
            return None
        if len(rest) != 2 or rest[0] != rest[1]:
            return None
        sort = rest[0]
        if sort == 'T':
            return ('any', rm_first)
        if sort == 'BV':
            return ('bv', rm_first)
        if sort == 'FP':
            return ('fp', rm_first)
        if sort == 'Real':
            return ('real', rm_first)
        return None

    def named_ctors(self):
        """Every kind with a named C++ constructor of a fixed or n-ary arity and no indices."""
        for k in self.kinds:
            if not k['c'] or k['indices'] != 0 or k['c'] == 'mk_fp':
                continue
            yield k

    def emit_kind_ctors_hpp(self):
        lines = [HEADER, '#ifndef STP_API_GEN_KIND_CTORS_HPP', '#define STP_API_GEN_KIND_CTORS_HPP', '',
                 '// Included by <stp/stp.hpp> inside namespace stp::api, after Term and the literal',
                 '// templates are declared. One named constructor per kind; the n-ary kinds get a',
                 '// binary, a vector and an initializer_list form; the literal overloads follow',
                 '// kinds.toml signatures (an integer beside a BV/Real/any-sorted term, a floating',
                 '// number beside an FP/Real/any-sorted term, a RoundingMode for an RM operand).', '']
        for k in self.named_ctors():
            c = k['c']
            lo, hi = arity_bounds(k['arity'])
            operands, _ = parse_sig(k['sig'])
            rm_first = bool(operands) and operands[0] == 'RM'
            lines.append('// %s: %s' % (k['name'], k['sig']))
            if hi == -1:
                lines.append('STP_API_EXPORT Term %s(const std::vector<Term>& args);' % c)
                lines.append('STP_API_EXPORT Term %s(std::initializer_list<Term> args);' % c)
                if lo <= 2:
                    lines.append('STP_API_EXPORT Term %s(const Term& a, const Term& b);' % c)
                if lo <= 1:
                    lines.append('STP_API_EXPORT Term %s(const Term& a);' % c)
            else:
                params = ', '.join('const Term& %s' % ('rm' if (i == 0 and rm_first) else 'abcd'[i - (1 if rm_first else 0)])
                                   for i in range(lo))
                lines.append('STP_API_EXPORT Term %s(%s);' % (c, params))
                if rm_first:
                    params2 = ', '.join(['RoundingMode rm'] + ['const Term& %s' % 'abcd'[i] for i in range(lo - 1)])
                    lines.append('STP_API_EXPORT Term %s(%s);' % (c, params2))
            lc = self.literal_class(k)
            if lc:
                cls, rmf = lc
                prefix_t = 'const Term& rm, ' if rmf else ''
                prefix_e = 'RoundingMode rm, ' if rmf else ''
                fams = []
                if cls in ('any', 'bv', 'real'):
                    fams.append(('I', 'if_integral<I>'))
                if cls in ('any', 'fp', 'real'):
                    fams.append(('F', 'if_floating<F>'))
                for tv, cond in fams:
                    for prefix in ([prefix_t, prefix_e] if rmf else ['']):
                        lines.append('template <class %s, %s = 0> STP_API_EXPORT_INLINE Term %s(%sconst Term& a, %s b);' % (tv, cond, c, prefix, tv))
                        lines.append('template <class %s, %s = 0> STP_API_EXPORT_INLINE Term %s(%s%s a, const Term& b);' % (tv, cond, c, prefix, tv))
            lines.append('')
        lines += ['#endif', '']
        self.write('include/stp/api/gen/kind_ctors.hpp', '\n'.join(lines))

    def emit_kind_ctors_inc(self):
        lines = [HEADER, '// Named constructor definitions; included by lib/Api/Constructors.cpp inside namespace stp::api.', '']
        for k in self.named_ctors():
            c = k['c']
            kind = 'Kind::' + k['name']
            lo, hi = arity_bounds(k['arity'])
            operands, _ = parse_sig(k['sig'])
            rm_first = bool(operands) and operands[0] == 'RM'
            if hi == -1:
                lines.append('Term %s(const std::vector<Term>& args) { return detail::mk_named(%s, %s, args); }' % (c, kind, cstr(c)))
                lines.append('Term %s(std::initializer_list<Term> args) { return detail::mk_named(%s, %s, std::vector<Term>(args)); }' % (c, kind, cstr(c)))
                if lo <= 2:
                    lines.append('Term %s(const Term& a, const Term& b) { return detail::mk_named(%s, %s, {a, b}); }' % (c, kind, cstr(c)))
                if lo <= 1:
                    lines.append('Term %s(const Term& a) { return detail::mk_named(%s, %s, {a}); }' % (c, kind, cstr(c)))
            else:
                names = ['rm' if (i == 0 and rm_first) else 'abcd'[i - (1 if rm_first else 0)] for i in range(lo)]
                params = ', '.join('const Term& %s' % n for n in names)
                lines.append('Term %s(%s) { return detail::mk_named(%s, %s, {%s}); }' % (c, params, kind, cstr(c), ', '.join(names)))
                if rm_first:
                    params2 = ', '.join(['RoundingMode rm'] + ['const Term& %s' % n for n in names[1:]])
                    lines.append('Term %s(%s) { return detail::mk_named(%s, %s, {detail::rm_term(%s, rm), %s}); }' % (
                        c, params2, kind, cstr(c), names[1], ', '.join(names[1:])))
        self.write('lib/Api/gen/kind_ctors.inc', '\n'.join(lines) + '\n')

    def emit_kind_ctor_templates(self):
        """The literal-overload template definitions, included by stp.hpp after the detail hooks."""
        lines = [HEADER, '#ifndef STP_API_GEN_KIND_CTOR_TEMPLATES_HPP', '#define STP_API_GEN_KIND_CTOR_TEMPLATES_HPP', '']
        for k in self.named_ctors():
            lc = self.literal_class(k)
            if not lc:
                continue
            c = k['c']
            cls, rmf = lc
            fams = []
            if cls in ('any', 'bv', 'real'):
                fams.append(('I', 'if_integral<I>', 'detail::int_literal'))
            if cls in ('any', 'fp', 'real'):
                fams.append(('F', 'if_floating<F>', 'detail::float_literal'))
            for tv, cond, conv in fams:
                if rmf:
                    lines.append('template <class %s, %s> Term %s(const Term& rm, const Term& a, %s b) { return %s(rm, a, %s(a, b, rm)); }' % (tv, cond, c, tv, c, conv))
                    lines.append('template <class %s, %s> Term %s(const Term& rm, %s a, const Term& b) { return %s(rm, %s(b, a, rm), b); }' % (tv, cond, c, tv, c, conv))
                    lines.append('template <class %s, %s> Term %s(RoundingMode rm, const Term& a, %s b) { return %s(detail::rm_term(a, rm), a, b); }' % (tv, cond, c, tv, c))
                    lines.append('template <class %s, %s> Term %s(RoundingMode rm, %s a, const Term& b) { return %s(detail::rm_term(b, rm), a, b); }' % (tv, cond, c, tv, c))
                else:
                    lines.append('template <class %s, %s> Term %s(const Term& a, %s b) { return %s(a, %s(a, b)); }' % (tv, cond, c, tv, c, conv))
                    lines.append('template <class %s, %s> Term %s(%s a, const Term& b) { return %s(%s(b, a), b); }' % (tv, cond, c, tv, c, conv))
        lines += ['', '#endif', '']
        self.write('include/stp/api/gen/kind_ctor_templates.hpp', '\n'.join(lines))

    COUNT_FIRST = ('AND', 'OR', 'XOR', 'DISTINCT')

    def emit_kind_ctors_h(self):
        lines = [HEADER, '#ifndef STP_API_GEN_KIND_CTORS_H', '#define STP_API_GEN_KIND_CTORS_H', '',
                 '/* Named C constructors for the non-indexed kinds (kinds.toml). Every one returns a',
                 ' * term the caller owns (+1), NULL on error with the manager\'s record set, and',
                 ' * NULL without a record when an argument is NULL. Indexed kinds (extract, the',
                 ' * to_fp family, fp.to_ubv/sbv) are declared in <stp/stp.h> by hand. */', '']
        for k in self.named_ctors():
            c = c_name(k['c'])
            lo, hi = arity_bounds(k['arity'])
            operands, _ = parse_sig(k['sig'])
            rm_first = bool(operands) and operands[0] == 'RM'
            if hi == -1:
                if k['name'] in self.COUNT_FIRST:
                    lines.append('STP_API stp_term %s(stp_tm tm, size_t n, const stp_term* args);' % c)
                    lines.append('STP_API stp_term %s2(stp_tm tm, stp_term a, stp_term b);' % c)
                else:
                    lines.append('STP_API stp_term %s(stp_tm tm, stp_term a, stp_term b);' % c)
                    lines.append('STP_API stp_term %s_n(stp_tm tm, size_t n, const stp_term* args);' % c)
            else:
                names = ['rm' if (i == 0 and rm_first) else 'abcd'[i - (1 if rm_first else 0)] for i in range(lo)]
                lines.append('STP_API stp_term %s(stp_tm tm, %s);' % (c, ', '.join('stp_term %s' % n for n in names)))
        lines += ['', '#endif', '']
        self.write('include/stp/api/gen/kind_ctors.h', '\n'.join(lines))

    def emit_kind_ctors_c_inc(self):
        lines = [HEADER, '// Named C constructor definitions; included by lib/Api/c/stp_c.cpp.', '']
        for k in self.named_ctors():
            c = c_name(k['c'])
            kind = 'STP_KIND_' + k['name']
            lo, hi = arity_bounds(k['arity'])
            operands, _ = parse_sig(k['sig'])
            rm_first = bool(operands) and operands[0] == 'RM'
            # Each goes through named_ctor (lib/Api/c/stp_c.cpp) under its own
            # name, so that an error record names the function the caller called.
            pair = 'stp_term %s(stp_tm tm, stp_term a, stp_term b) { const stp_term args[] = {a, b}; return named_ctor(tm, "%s", %s, 2, args); }'
            array = 'stp_term %s(stp_tm tm, size_t n, const stp_term* args) { return named_ctor(tm, "%s", %s, n, args); }'
            if hi == -1:
                if k['name'] in self.COUNT_FIRST:
                    lines.append(array % (c, c, kind))
                    lines.append(pair % (c + '2', c + '2', kind))
                else:
                    lines.append(pair % (c, c, kind))
                    lines.append(array % (c + '_n', c + '_n', kind))
            else:
                names = ['rm' if (i == 0 and rm_first) else 'abcd'[i - (1 if rm_first else 0)] for i in range(lo)]
                params = ', '.join('stp_term %s' % n for n in names)
                lines.append('stp_term %s(stp_tm tm, %s) { const stp_term args[] = {%s}; return named_ctor(tm, "%s", %s, %d, args); }' % (
                    c, params, ', '.join(names), c, kind, lo))
        self.write('lib/Api/gen/kind_ctors_c.inc', '\n'.join(lines) + '\n')

    # ----------------------------------------------------------------- options

    @staticmethod
    def default_text(o):
        d = o['default']
        if isinstance(d, bool):
            return 'true' if d else 'false'
        if isinstance(d, list):
            return ','.join(d)
        return str(d)

    @staticmethod
    def python_key(name):
        return name.replace('-', '_').replace('.', '_')

    def emit_options_hpp(self):
        lines = [HEADER, '#ifndef STP_API_GEN_OPTIONS_HPP', '#define STP_API_GEN_OPTIONS_HPP', '',
                 '#include <cstdint>', '', 'namespace stp {', 'namespace api {', '',
                 '/// The stable option tier as a typed enum (options.toml), each value pinned by its id.',
                 'enum class Option : std::uint16_t {']
        stable = self.stable_options()
        for o in stable:
            lines.append('  %s = %d,  ///< %s' % (o['name'].upper().replace('-', '_').replace('.', '_'), o['id'], o['name']))
        lines.append('  NUM_STABLE_OPTIONS = %d' % len(stable))
        lines.append('};')
        lines += ['', '}  // namespace api', '}  // namespace stp', '', '#endif', '']
        self.write('include/stp/api/gen/options.hpp', '\n'.join(lines))

    def emit_options_h(self):
        lines = [HEADER, '#ifndef STP_API_GEN_OPTIONS_H', '#define STP_API_GEN_OPTIONS_H', '',
                 'typedef enum stp_option {']
        stable = self.stable_options()
        for o in stable:
            lines.append('  STP_OPT_%s = %d,' % (o['name'].upper().replace('-', '_').replace('.', '_'), o['id']))
        lines.append('  STP_NUM_STABLE_OPTIONS = %d,' % len(stable))
        lines.append('  STP_OPT_MAX_ENUM = 0x7fffffff /* not an option: widens the enum to int (stp.h) */')
        lines.append('} stp_option;')
        lines += ['', '#endif', '']
        self.write('include/stp/api/gen/options.h', '\n'.join(lines))

    def cli_default_text(self, o):
        """The row's cli_default as its default is spelt (a Boolean true/false), or None."""
        if 'cli_default' not in o:
            return None
        v = o['cli_default']
        if isinstance(v, bool):
            return 'true' if v else 'false'
        return str(v)

    def emit_option_table(self):
        lines = [HEADER, '// OptionSpec rows, in registry order. String arrays first, then the rows.', '']
        rows = []
        for i, o in enumerate(self.options):
            values = o.get('values', [])
            aliases = o.get('aliases', [])
            excludes = o.get('excludes', [])
            implies = o.get('implies', {})
            implies_pairs = []
            implies_note = ''
            if isinstance(implies, dict):
                for key, val in implies.items():
                    implies_pairs.append((key, 'true' if val is True else 'false' if val is False else str(val)))
            else:
                implies_note = str(implies)
            lines.append('static const char* const kOptValues%d[] = { %s };' % (i, ', '.join([cstr(v) for v in values] + ['nullptr'])))
            lines.append('static const char* const kOptAliases%d[] = { %s };' % (i, ', '.join([cstr(v) for v in aliases] + ['nullptr'])))
            lines.append('static const char* const kOptExcludes%d[] = { %s };' % (i, ', '.join([cstr(v) for v in excludes] + ['nullptr'])))
            lines.append('static const char* const kOptImplies%d[] = { %s };' % (i, ', '.join([cstr(x) for pair in implies_pairs for x in pair] + ['nullptr'])))
            rng = o.get('range', {})
            implied_by = o.get('implied_by', {})
            ib_opt = ib_val = None
            for key, val in implied_by.items():
                ib_opt, ib_val = key, ('true' if val is True else 'false' if val is False else str(val))
            req = o.get('requires', {})
            engine = o.get('engine', {})
            rows.append('  { %s, %s, OptType::%s, %s, %s, %s, %s, %s, kOptValues%d, %d, Tier::%s, Settable::%s, OptionScope::%s, %s, %s, kOptAliases%d, %d, %s, %s, %s, %s, %s, kOptExcludes%d, %d, kOptImplies%d, %d, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %d },' % (
                cstr(o['name']), cstr(self.python_key(o['name'])), o['type'].upper(), cstr(self.default_text(o)),
                'true' if 'min' in rng else 'false', c_i64(rng.get('min', 0)),
                'true' if 'max' in rng else 'false', c_i64(rng.get('max', 0)),
                i, len(values),
                o['tier'].upper(), o['settable'].upper().replace('-', '_'), o['scope'].upper(),
                cstr(o['category']), cstr(o['help']),
                i, len(aliases),
                cstr(o.get('short')), cstr(o.get('negation')), cstr(o.get('follows')),
                cstr(ib_opt), cstr(ib_val),
                i, len(excludes), i, len(implies_pairs),
                cstr(implies_note or None),
                cstr(req.get('build')), cstr(req.get('option')), cstr(req.get('value')),
                cstr(o.get('latched_by')), cstr(o.get('sentinel')),
                cstr(engine.get('field') or engine.get('custom') or engine.get('none')),
                'true' if 'engine' in o else 'false',
                cstr(o.get('cli_form', 'value')), cstr(o.get('cli_bad_value')),
                'true' if 'cli_range' in o else 'false',
                c_i64(o.get('cli_range', {}).get('min', 0)), c_i64(o.get('cli_range', {}).get('max', 0)),
                cstr(o.get('cli_below_min')), cstr(o.get('cli_above_max')),
                'true' if o.get('cli_take_last', False) else 'false',
                'true' if o.get('cli_empty') == 'unset' else 'false',
                cstr(o.get('cli_help')), cstr(self.cli_default_text(o)),
                o.get('id', -1)))
        lines.append('')
        lines.append('static const OptionSpec kOptionSpecs[] = {')
        lines += rows
        lines.append('};')
        lines.append('static const std::size_t kNumOptionSpecs = %d;' % len(self.options))
        index = {o['name']: i for i, o in enumerate(self.options)}
        stable = self.stable_options()
        lines.append('// The registry row of each stable id (Option / stp_option value).')
        lines.append('static const std::size_t kStableOptionRows[] = { %s };'
                     % ', '.join(str(index[o['name']]) for o in stable))
        lines.append('static const std::size_t kNumStableOptions = %d;' % len(stable))
        self.write('lib/Api/gen/option_table.inc', '\n'.join(lines) + '\n')

    def emit_option_apply(self):
        """The registry -> engine switch. Each row's `engine` table says how the value reaches
        UserDefinedFlags: { field, invert?, kind? } assigns a flag member; { custom = "name" }
        calls a hand-written applier; { none = "why" } has no engine effect (frontend rows)."""
        lines = [HEADER, '// Included by lib/Api/OptionApply.cpp inside apply_option_to_engine(); `t` is the',
                 '// EngineTarget, `v` the validated OptionValue, `spec` the row. Returns false when the',
                 '// row has no engine mapping yet (the completeness test lists those).', '',
                 'switch (index) {']
        unmapped = []
        for i, o in enumerate(self.options):
            e = o.get('engine')
            if not e:
                unmapped.append(o['name'])
                lines.append('  case %d: /* %s */ return false;' % (i, o['name']))
                continue
            if 'none' in e:
                lines.append('  case %d: /* %s: %s */ return true;' % (i, o['name'], e['none']))
            elif 'custom' in e:
                lines.append('  case %d: /* %s */ return custom_%s(t, spec, v);' % (i, o['name'], e['custom']))
            else:
                field = e['field']
                invert = e.get('invert', False)
                t = o['type']
                if t == 'bool':
                    lines.append('  case %d: /* %s */ detail::assign_flag(t.flags.%s, %sas_bool(v)); return true;' % (
                        i, o['name'], field, '!' if invert else ''))
                elif t in ('int', 'uint'):
                    lines.append('  case %d: /* %s */ detail::assign_flag(t.flags.%s, as_int(v)); return true;' % (i, o['name'], field))
                elif t == 'mode':
                    lines.append('  case %d: /* %s */ t.flags.%s = as_mode<decltype(t.flags.%s)>(v); return true;' % (i, o['name'], field, field))
                else:
                    raise SystemExit('options.toml: %s: a %s-typed option needs engine.custom' % (o['name'], t))
        lines.append('  default: return false;')
        lines.append('}')
        lines.append('')
        lines.append('// unmapped: %d' % len(unmapped))
        self.write('lib/Api/gen/option_apply.inc', '\n'.join(lines) + '\n')
        self.unmapped = unmapped

    def emit_option_defaults(self):
        """The engine's default of every field-mapped entry, read from a fresh UserDefinedFlags, so
        a test can hold the registry's defaults to the engine's."""
        lines = [HEADER, '// Included by lib/Api/Options.cpp: `flag_text` renders a UserDefinedFlags member as the',
                 '// registry spells it (true/false, an integer, auto/on/off).', '']
        rows = []
        for o in self.options:
            e = o.get('engine', {})
            if 'field' not in e:
                continue
            expr = 'f.%s' % e['field']
            if e.get('invert', False):
                expr = '!(%s)' % expr
            rows.append('  { %s, [](const UserDefinedFlags& f) { return flag_text(%s); } },' % (cstr(o['name']), expr))
        lines.append('static const DefaultCheck kDefaultChecks[] = {')
        lines += rows
        lines.append('};')
        lines.append('static const std::size_t kNumDefaultChecks = %d;' % len(rows))
        # The values the engine field of each numeric entry can hold, so a test can
        # hold the registry's range to them: an accepted value is never truncated.
        ranges = []
        for o in self.options:
            e = o.get('engine', {})
            if 'field' not in e or o['type'] not in ('int', 'uint'):
                continue
            t = 'decltype(UserDefinedFlags::%s)' % e['field']
            ranges.append('  { %s, static_cast<std::int64_t>(std::numeric_limits<%s>::min()), '
                          'static_cast<std::uint64_t>(std::numeric_limits<%s>::max()) },' % (cstr(o['name']), t, t))
        lines.append('')
        lines.append('static const FieldRange kFieldRanges[] = {')
        lines += ranges
        lines.append('};')
        lines.append('static const std::size_t kNumFieldRanges = %d;' % len(ranges))
        self.write('lib/Api/gen/option_defaults.inc', '\n'.join(lines) + '\n')

    def emit_cli_table(self):
        """The command-line data of tools/stp that is not a per-entry column: the --help groups in
        order, the category -> group map, the backend-flag aliases and the frontend rows."""
        lines = [HEADER, '// Included by lib/Api/Options.cpp. The rows tools/stp registers besides the option',
                 '// entries themselves (main.cpp walks kOptionSpecs for those).', '']
        lines.append('static const char* const kCliGroups[] = { %s };' % ', '.join(cstr(g['name']) for g in self.cli_groups))
        lines.append('static const std::size_t kNumCliGroups = %d;' % len(self.cli_groups))
        lines.append('static const CliCategory kCliCategories[] = {')
        for c in self.categories:
            lines.append('  { %s, %s },' % (cstr(c['name']), cstr(c['group'])))
        lines.append('};')
        lines.append('static const std::size_t kNumCliCategories = %d;' % len(self.categories))
        lines.append('static const CliAlias kCliAliases[] = {')
        for a in self.aliases:
            lines.append('  { %s, %s, %s, %s },' % (cstr(a['name']), cstr(a['of']), cstr(a['value']), cstr(a['help'])))
        lines.append('};')
        lines.append('static const std::size_t kNumCliAliases = %d;' % len(self.aliases))
        for i, r in enumerate(self.frontend):
            lines.append('static const char* const kCliFrontendExcludes%d[] = { %s };' % (
                i, ', '.join([cstr(x) for x in r.get('excludes', [])] + ['nullptr'])))
        lines.append('static const CliFrontend kCliFrontend[] = {')
        for i, r in enumerate(self.frontend):
            lines.append('  { %s, %s, %s, %s, %s, %s, kCliFrontendExcludes%d, %d },' % (
                cstr(r['key']), cstr(r['cli']), cstr(r['kind']), cstr(r.get('group')), cstr(r['help']), cstr(r['api']),
                i, len(r.get('excludes', []))))
        lines.append('};')
        lines.append('static const std::size_t kNumCliFrontend = %d;' % len(self.frontend))
        self.write('lib/Api/gen/cli_table.inc', '\n'.join(lines) + '\n')

    # ----------------------------------------------------------------- errors

    def emit_errors_hpp(self):
        lines = [HEADER, '#ifndef STP_API_GEN_ERRORS_HPP', '#define STP_API_GEN_ERRORS_HPP', '',
                 '#include <cstdint>', '', 'namespace stp {', 'namespace api {', '',
                 '/// Error codes (errors.toml). RESOURCE and INTERNAL are the two unsafe codes.',
                 'enum class ErrorCode : std::uint16_t {']
        for e in self.errors:
            lines.append('  %s = %d,' % (e['name'], e['value']))
        lines.append('};')
        lines += ['', '}  // namespace api', '}  // namespace stp', '', '#endif', '']
        self.write('include/stp/api/gen/errors.hpp', '\n'.join(lines))

    def emit_errors_h(self):
        lines = [HEADER, '#ifndef STP_API_GEN_ERRORS_H', '#define STP_API_GEN_ERRORS_H', '',
                 'typedef enum stp_error_code {']
        for e in self.errors:
            lines.append('  STP_ERR_%s = %d,' % (e['name'], e['value']))
        lines.append('  STP_ERR_MAX_ENUM = 0x7fffffff /* not a code: widens the enum to int (stp.h) */')
        lines.append('} stp_error_code;')
        lines += ['', '#endif', '']
        self.write('include/stp/api/gen/errors.h', '\n'.join(lines))

    def emit_error_table(self):
        lines = [HEADER]
        for e in self.errors:
            lines.append('  { ErrorCode::%s, %s, %s, %s, %s },' % (
                e['name'], cstr(e['name']), 'true' if e['recoverable'] else 'false', cstr(e['message']), cstr(e['python'])))
        self.write('lib/Api/gen/error_table.inc', '\n'.join(lines) + '\n')

    # ----------------------------------------------------------------- statistics

    def emit_stat_table(self):
        lines = [HEADER]
        for s in self.stats:
            lines.append('  { %s, StatType::%s, Tier::%s, %s },' % (
                cstr(s['name']), s['type'].upper(), s['tier'].upper(), cstr(s['help'])))
        self.write('lib/Api/gen/stat_table.inc', '\n'.join(lines) + '\n')

    # ----------------------------------------------------------------- python

    def emit_python(self):
        lines = [HEADER.replace('//', '#'), '# Cython enum declarations for stp._core (included by _core.pxd).', '',
                 'cdef extern from "stp/stp.h":', '    ctypedef enum stp_kind:']
        for k in self.kinds:
            lines.append('        STP_KIND_%s' % k['name'])
        lines.append('    ctypedef enum stp_error_code:')
        for e in self.errors:
            lines.append('        STP_ERR_%s' % e['name'])
        lines.append('    ctypedef enum stp_option:')
        for o in self.stable_options():
            lines.append('        STP_OPT_%s' % o['name'].upper().replace('-', '_').replace('.', '_'))
        self.write('python/_gen_enums.pxi', '\n'.join(lines) + '\n')

        py = [HEADER.replace('//', '#'), '"""The generated Python enums: Kind, Option (stable tier) and ErrorCode."""', '',
              'import enum', '', '', 'class Kind(enum.IntEnum):']
        for k in self.kinds:
            py.append('    %s = %d' % (k['name'], k['id']))
        py += ['', '', 'class Option(enum.IntEnum):']
        for o in self.stable_options():
            py.append('    %s = %d' % (o['name'].upper().replace('-', '_').replace('.', '_'), o['id']))
        py += ['', '', 'class ErrorCode(enum.IntEnum):']
        for e in self.errors:
            py.append('    %s = %d' % (e['name'], e['value']))
        py += ['', '', 'SMTLIB_NAMES = {']
        for k in self.kinds:
            py.append('    Kind.%s: %s,' % (k['name'], cstr(k['smtlib'])))
        py.append('}')
        py += ['', 'OPTION_NAMES = (']
        for o in self.options:
            py.append('    %s,' % cstr(o['name']))
        py.append(')')
        self.write('python/_gen_kinds.py', '\n'.join(py) + '\n')

    def run(self):
        self.emit_kinds_hpp()
        self.emit_kinds_h()
        self.emit_kind_table()
        self.emit_kind_ctors_hpp()
        self.emit_kind_ctor_templates()
        self.emit_kind_ctors_inc()
        self.emit_kind_ctors_h()
        self.emit_kind_ctors_c_inc()
        self.emit_options_hpp()
        self.emit_options_h()
        self.emit_option_table()
        self.emit_option_apply()
        self.emit_option_defaults()
        self.emit_cli_table()
        self.emit_errors_hpp()
        self.emit_errors_h()
        self.emit_error_table()
        self.emit_stat_table()
        self.emit_python()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--tables', required=True)
    ap.add_argument('--out', required=True)
    ap.add_argument('--check', action='store_true', help='report files that would change; write nothing')
    ap.add_argument('--list-unmapped', action='store_true', help='print the options without an engine mapping')
    ap.add_argument('--toml-subset', action='store_true',
                    help='read the tables with the subset parser older interpreters use, even where tomllib exists')
    ap.add_argument('--self-test', action='store_true',
                    help='compare what tomllib and the subset parser read from every table; write nothing')
    args = ap.parse_args()
    names = ('kinds', 'options', 'errors', 'statistics')
    if args.self_test:
        if tomllib is None:
            print('self-test: this interpreter has no tomllib to compare against')
            return 0
        differ = [name for name in names
                  if load_toml(os.path.join(args.tables, name + '.toml')) !=
                  load_toml(os.path.join(args.tables, name + '.toml'), subset=True)]
        if differ:
            print('the subset parser reads these tables differently from tomllib: ' + ', '.join(differ))
            return 1
        return 0
    tables = {name: load_toml(os.path.join(args.tables, name + '.toml'), subset=args.toml_subset)
              for name in names}
    em = Emitter(tables, args.out, args.check)
    em.run()
    if args.list_unmapped:
        for name in em.unmapped:
            print(name)
    if args.check and em.changed:
        print('generated files out of date: ' + ', '.join(em.changed))
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
