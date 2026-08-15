#!/usr/bin/env python3

# AUTHORS: Vijay Ganesh, David L. Dill BEGIN DATE: November, 2005
#
# Permission is hereby granted, free of charge, to any person obtaining
# a copy of this software and associated documentation files (the
# "Software"), to deal in the Software without restriction, including
# without limitation the rights to use, copy, modify, merge, publish,
# distribute, sublicense, and/or sell copies of the Software, and to
# permit persons to whom the Software is furnished to do so, subject to
# the following conditions:
#
# The above copyright notice and this permission notice shall be
# included in all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
# EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
# MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
# NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
# LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
# OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
# WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
#
# given a file containing kind names, one per line produces .h and .cpp
# files for the kinds.

import os
import re
import sys
import time

# The .kinds grammar. Both patterns are deliberately ASCII-only: a stray
# non-ASCII byte must never widen \w and so change how a line parses.
#
# "Categories:" is searched for anywhere in the line, while a kind line is
# anchored: three whitespace-delimited alphanumeric fields followed by the
# rest of the line. Lines beginning with '#' and blank lines therefore fall
# through and are ignored. The trailing "\s+(.*)" still matches when a kind
# has no categories, because the line terminator supplies the whitespace and
# '.' does not match a newline.
CATEGORIES_RE = re.compile(r"Categories:\s+(.*)", re.ASCII)
KIND_RE = re.compile(r"^(\w+)\s+(\w+)\s+(\w+|-)\s+(.*)", re.ASCII)


def parse_args(argv):
    """Accept the option spellings the build (and Getopt::Long) uses."""
    fname = "ASTKind.kinds"
    timestamp = True

    i = 0
    while i < len(argv):
        arg = argv[i]
        if arg == "--file":
            i += 1
            if i >= len(argv):
                sys.exit("Option file requires an argument\n")
            fname = argv[i]
        elif arg.startswith("--file="):
            fname = arg[len("--file="):]
        elif arg == "--timestamp":
            timestamp = True
        elif arg in ("--no-timestamp", "--notimestamp"):
            timestamp = False
        else:
            sys.exit("Unknown option: %s\n" % arg)
        i += 1

    return fname, timestamp


def source_date_epoch():
    """Reproduce Perl's `$ENV{SOURCE_DATE_EPOCH} || time`.

    Unset, empty and "0" are all false in Perl, so each falls back to the
    current time; anything else is numified the way Perl numifies a string,
    i.e. by taking its leading numeric prefix.
    """
    value = os.environ.get("SOURCE_DATE_EPOCH")
    if not value or value == "0":
        return time.time()

    match = re.match(r"\s*[-+]?(?:\d+\.?\d*|\.\d+)(?:[eE][-+]?\d+)?", value)
    if not match:
        return 0.0
    return float(match.group(0))


def read_kind_defs(fname):
    try:
        # surrogateescape keeps any byte round-trippable, so an odd encoding
        # in the input cannot make us fail where the Perl version did not.
        with open(fname, "r", encoding="utf-8", errors="surrogateescape") as f:
            return f.readlines()
    except OSError as e:
        sys.exit("Cannot open .kinds file %s: %s\n" % (fname, e.strerror))


def split_fields(kindlines):
    """Create the lists of things indexed by kinds."""
    kindnames = []
    cat_bits = []
    category_names = []
    cat_index = {}

    for line in kindlines:
        match = CATEGORIES_RE.search(line)
        if match:
            category_names = match.group(1).split()
            for i, name in enumerate(category_names):
                cat_index[name] = i
            continue

        match = KIND_RE.match(line)
        if match:
            kindnames.append(match.group(1))
            kind_cats = match.group(4).split()
            # build a bit vector of categories. An unknown category name is
            # undef in Perl, which numifies to 0, so it sets bit 0.
            kind_cat_bits = 0
            for name in kind_cats:
                kind_cat_bits |= 1 << cat_index.get(name, 0)
            cat_bits.append(kind_cat_bits)

    return kindnames, cat_bits, category_names, cat_index


def gen_h_file(now, kindnames, category_names, cat_index):
    try:
        hfile = open("ASTKind.h", "w", encoding="utf-8",
                     errors="surrogateescape", newline="\n")
    except OSError as e:
        sys.exit("Cannot open .h file: %s\n" % e.strerror)

    with hfile:
        hfile.write(
            "#ifndef TESTKINDS_H\n"
            "#define TESTKINDS_H\n"
            "// Generated automatically by genkinds.py from ASTKind.kinds%s.\n"
            "// Do not edit\n"
            "#include <iostream>\n"
            "namespace stp {\n  typedef enum {\n" % now
        )

        last = len(kindnames) - 1
        for i, kindname in enumerate(kindnames):
            hfile.write("  " + kindname)
            if i != last:
                hfile.write(",")
            hfile.write("\n")

        hfile.write(
            "} Kind;\n\n"
            "extern unsigned char _kind_categories[];\n\n"
        )

        # For category named "cat", generate functions "bool is_cat_kind(k);"

        for catname in category_names:
            kind_cat_bit = 1 << cat_index.get(catname, 0)
            hfile.write(
                "inline bool is_%s_kind(Kind k) { return (_kind_categories[k]"
                " & %d); }\n\n" % (catname, kind_cat_bit)
            )

        hfile.write(
            "extern const char *_kind_names[];\n\n"
            "/** Prints symbolic name of kind */\n"
            "inline std::ostream& operator<<(std::ostream &os, const Kind"
            " &kind) { os << _kind_names[kind]; return os; }\n"
            "\n\n"
            "}  // end namespace\n"
            "\n\n#endif\n"
        )


def gen_cpp_file(now, kindnames, cat_bits):
    """Generate the .cpp file."""
    try:
        cppfile = open("ASTKind.cpp", "w", encoding="utf-8",
                       errors="surrogateescape", newline="\n")
    except OSError as e:
        sys.exit("Cannot open .h file: %s\n" % e.strerror)

    with cppfile:
        cppfile.write(
            "// Generated automatically by genkinds.py from ASTKind.kinds%s.\n"
            "// Do not edit\n"
            "namespace stp {\n"
            "#if defined(__GNUC__) || defined(__clang__)\n\n"
            "__attribute__((visibility(\"default\")))\n\n"
            "#endif\n\n"
            "const char * _kind_names[] =  {\n" % now
        )

        for kindname in kindnames:
            cppfile.write("   \"" + kindname + "\",\n")
        cppfile.write("};\n\n")

        # category bits
        cppfile.write(
            "#if defined(__GNUC__) || defined(__clang__)\n\n"
            "__attribute__((visibility(\"default\")))\n\n"
            "#endif\n\n"
            "unsigned char _kind_categories[] = {\n"
        )

        for i, kindname in enumerate(kindnames):
            cppfile.write("   %d, //%s\n" % (cat_bits[i], kindname))
        cppfile.write(
            "};\n"
            "\n}  // end namespace\n"
        )


def main(argv):
    fname, timestamp = parse_args(argv)

    if timestamp:
        now = " " + time.asctime(time.localtime(source_date_epoch()))
    else:
        now = ""

    kindlines = read_kind_defs(fname)
    kindnames, cat_bits, category_names, cat_index = split_fields(kindlines)
    gen_h_file(now, kindnames, category_names, cat_index)
    gen_cpp_file(now, kindnames, cat_bits)


if __name__ == "__main__":
    main(sys.argv[1:])
