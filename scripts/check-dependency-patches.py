#!/usr/bin/env python3
"""Fail if STP changes a dependency's sources at build time.

Every dependency STP builds is fetched at a pinned commit and built as it is.
When STP needs a dependency to be different, the change is a commit in STP's
fork of it (github.com/stp/<name>) and the pin moves to that commit -- it is
never a patch file, a PATCH_COMMAND, or CMake that rewrites the fetched
sources. A change made at build time is invisible to anyone reading the
dependency, has to be re-applied on every bump with nothing to say where it
stopped applying, and gives two copies of the dependency that both call
themselves the pinned revision.

This looks for the ways a build can do that:

  * a tracked *.patch or *.diff file;
  * PATCH_COMMAND, `git apply` or `patch -p` in the build or CI scripts;
  * CMake that reads a fetched dependency's sources whole (to rewrite them)
    or writes into its source tree.

Run it from anywhere in the repository; it checks the files git tracks there.
ALLOWED lists the exceptions still being worked off, and each has to name why.
An entry that no longer matches anything is reported too, so the list cannot
outlive what it excuses.
"""

import re
import subprocess
import sys
from pathlib import Path

# (path, rule) -> why it is still allowed. Remove an entry in the change that
# moves its patch into the fork.
ALLOWED = {
    ('cmake/deps-utils/highs-root-cut-log.patch', 'patch-file'):
        'HiGHS: draft #1247 rewrites this patch; it moves to a stp/HiGHS fork after that lands',
    ('cmake/deps-utils/patch-highs.cmake', 'apply'):
        'HiGHS: draft #1247 rewrites this patch; it moves to a stp/HiGHS fork after that lands',
    ('cmake/FindHiGHS.cmake', 'patch-command'):
        'HiGHS: draft #1247 rewrites this patch; it moves to a stp/HiGHS fork after that lands',
}

FIX = (
    'STP builds each dependency from a commit of its fork as it stands. Make '
    'the change a commit in the fork (github.com/stp/<name>, on the branch the '
    'pin names), and move the pin in cmake/Find<Name>.cmake to it -- see '
    '"Changing a dependency" in docs/code-guide.rst.'
)

# A dependency's source tree, as CMake names it: ExternalProject's
# <SOURCE_DIR> placeholder, the SOURCE_DIR a patch script is handed, or
# FetchContent's <name>_SOURCE_DIR. CMAKE_SOURCE_DIR, CMAKE_CURRENT_SOURCE_DIR,
# PROJECT_SOURCE_DIR and STP's own STP_*_SOURCE_DIR name STP's tree.
DEP_SOURCE = (r'(<SOURCE_DIR>|\$\{SOURCE_DIR\}'
              r'|\$\{(?!CMAKE_|PROJECT_|STP_)\w+_SOURCE_DIR\})')

# A variable set to a path inside one, possibly with the value on the next
# line: what PrepareUnorderedDense.cmake did before it read the header it
# rewrote.
DEP_PATH_VARIABLE = re.compile(
    r'\bset\s*\(\s*(\w+)\s+"?' + DEP_SOURCE, re.MULTILINE)

# Matched against whole CMake commands, joined onto one line, so that an
# argument on a continuation line counts.
CMAKE_RULES = [
    ('patch-command', re.compile(r'\bPATCH_COMMAND\b'),
     'PATCH_COMMAND changes the fetched sources before they are built'),
    ('apply', re.compile(r'\bgit\s+(-C\s+\S+\s+)?apply\b|\bpatch\s+-p'),
     'applies a patch'),
    ('rewrite', re.compile(r'\bfile\s*\(\s*READ\s+"?' + DEP_SOURCE),
     "reads a dependency's source file whole, which is how a rewrite starts"),
    ('rewrite', re.compile(
        r'\b(file\s*\(\s*(WRITE|APPEND|COPY|RENAME|CONFIGURE)\b|configure_file\s*\()'
        r'[^\n]*' + DEP_SOURCE),
     "writes into a dependency's source tree"),
    # cmake -E copy's destination is its last argument: what follows it is
    # the end of the command or the next keyword.
    ('rewrite', re.compile(
        r'\b(copy|copy_if_different|copy_directory|rename)\b'
        r'(\s+[^\s)]+)*?\s+"?' + DEP_SOURCE
        + r'[^\s")]*(?![^\s")])"?(?=\s*(\)|$|[A-Z][A-Z_]{2,}(\s|\)|$)))'),
     "copies a file into a dependency's source tree"),
]


def traced_rules(text):
    """Rules for the variables this file sets to a path in a dependency's
    source tree: reading or writing through one is the same as naming the
    path directly."""
    names = sorted({m.group(1) for m in DEP_PATH_VARIABLE.finditer(text)})
    if not names:
        return []
    via = r'\$\{(' + '|'.join(map(re.escape, names)) + r')\}'
    return [
        ('rewrite', re.compile(r'\bfile\s*\(\s*READ\s+"?' + via),
         "reads a dependency's source file whole, which is how a rewrite "
         "starts"),
        ('rewrite', re.compile(
            r'\b(file\s*\(\s*(WRITE|APPEND|COPY|RENAME|CONFIGURE)\b'
            r'|configure_file\s*\()[^\n]*' + via),
         "writes into a dependency's source tree"),
    ]

SCRIPT_RULES = [
    ('apply', re.compile(r'\bgit\s+apply\b|\bpatch\s+-p\d'),
     'applies a patch'),
]


def tracked_files():
    out = subprocess.run(['git', 'ls-files', '-z'], check=True,
                         capture_output=True).stdout
    return [p for p in out.decode().split('\0') if p]


def is_cmake(path):
    name = Path(path).name
    return (name == 'CMakeLists.txt' or name.endswith('.cmake')
            or name.endswith('.cmake.in'))


def is_script(path):
    return (path.startswith(('.github/', 'scripts/'))
            or Path(path).name in ('Dockerfile', 'configure.sh')
            or path.endswith('.sh'))


def code_of(line):
    """A shell or YAML line without a comment that starts it."""
    return '' if line.lstrip().startswith('#') else line


BRACKET_OPEN = re.compile(r'\[(=*)\[')


def cmake_code(text):
    """CMake text with its comments blanked out, line breaks kept so that
    offsets still map to lines. A '#' inside a quoted or bracket argument
    is part of the argument; '#[[...]]' is a bracket comment."""
    out, i, quoted = [], 0, False
    while i < len(text):
        ch = text[i]
        if quoted:
            out.append(ch)
            if ch == '\\' and i + 1 < len(text):
                out.append(text[i + 1])
                i += 1
            elif ch == '"':
                quoted = False
        elif ch == '"':
            quoted = True
            out.append(ch)
        elif ch == '[' and BRACKET_OPEN.match(text, i):
            close = ']' + BRACKET_OPEN.match(text, i).group(1) + ']'
            end = text.find(close, i)
            end = len(text) if end < 0 else end + len(close)
            out.append(text[i:end])
            i = end
            continue
        elif ch == '#':
            bracket = BRACKET_OPEN.match(text, i + 1)
            if bracket:
                close = ']' + bracket.group(1) + ']'
                end = text.find(close, i)
                end = len(text) if end < 0 else end + len(close)
            else:
                end = text.find('\n', i)
                end = len(text) if end < 0 else end
            out.append(''.join('\n' if c == '\n' else ' '
                               for c in text[i:end]))
            i = end
            continue
        else:
            out.append(ch)
        i += 1
    return ''.join(out)


def cmake_commands(code):
    """The (begin, end) offsets of each top-level command in cmake_code():
    from the command's name to its closing
    parenthesis. Parentheses inside quoted and bracket arguments do not
    count."""
    depth, begin, i, quoted = 0, None, 0, False
    while i < len(code):
        ch = code[i]
        if quoted:
            if ch == '\\':
                i += 1
            elif ch == '"':
                quoted = False
        elif ch == '"':
            quoted = True
        elif ch == '[' and BRACKET_OPEN.match(code, i):
            close = ']' + BRACKET_OPEN.match(code, i).group(1) + ']'
            end = code.find(close, i)
            i = len(code) if end < 0 else end + len(close)
            continue
        elif ch == '(':
            if depth == 0:
                name = re.search(r'\w+\s*$', code[:i])
                begin = name.start() if name else i
            depth += 1
        elif ch == ')' and depth:
            depth -= 1
            if depth == 0:
                yield begin, i + 1
        i += 1


def main():
    root = subprocess.run(['git', 'rev-parse', '--show-toplevel'], check=True,
                          capture_output=True, text=True).stdout.strip()
    findings = []
    for path in tracked_files():
        if path == 'scripts/check-dependency-patches.py':
            continue
        if path.endswith(('.patch', '.diff')):
            findings.append((path, 0, 'patch-file', 'a patch file'))
            continue
        try:
            text = (Path(root) / path).read_text(errors='replace')
        except (FileNotFoundError, IsADirectoryError):
            continue
        if is_cmake(path):
            rules = CMAKE_RULES + traced_rules(text)
        elif is_script(path):
            rules = SCRIPT_RULES
        else:
            continue
        if rules is SCRIPT_RULES:
            for number, line in enumerate(text.splitlines(), 1):
                for rule, pattern, what in rules:
                    if pattern.search(code_of(line)):
                        findings.append((path, number, rule, what))
                        break
            continue
        code = cmake_code(text)
        flat = code.replace('\n', ' ')
        seen = set()
        for begin, end in cmake_commands(code):
            for rule, pattern, what in rules:
                for match in pattern.finditer(flat, begin, end):
                    number = code.count('\n', 0, match.start()) + 1
                    if (number, rule) not in seen:
                        seen.add((number, rule))
                        findings.append((path, number, rule, what))

    used = set()
    failures = []
    for path, number, rule, what in findings:
        if (path, rule) in ALLOWED:
            used.add((path, rule))
        else:
            failures.append((path, number, what))

    stale = sorted(set(ALLOWED) - used)

    for path, number, what in failures:
        where = f'{path}:{number}' if number else path
        print(f'{where}: {what}')
    for path, rule in stale:
        print(f'{path}: allowed for "{rule}", but nothing there needs it any '
              f'more -- remove the entry from ALLOWED in '
              f'scripts/check-dependency-patches.py')
    if failures:
        print(f'\n{FIX}')
    if failures or stale:
        return 1

    for (path, rule), why in sorted(ALLOWED.items()):
        print(f'allowed: {path} ({rule}): {why}')
    print('No dependency is patched at build time beyond the entries above.')
    return 0


if __name__ == '__main__':
    sys.exit(main())
