#!/usr/bin/perl -w

#AUTHORS: Vijay Ganesh, David L. Dill BEGIN DATE: November, 2005
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 * LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
 * OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
#given a file containing kind names, one per line produces .h and .cpp
#files for the kinds.

use Getopt::Long;
my $fname = "ASTKind.kinds";
GetOptions ("file=s" => \$fname);

#globals
@kindnames = ();
$minkids = 0;
$maxkids = 0;
@cat_bits = ();
@category_names = ();
%cat_index = ();

$now = localtime time;

sub read_kind_defs {
    open(KFILE, "< $fname") || die "Cannot open .kinds file $fname: $!\n";
    @kindlines = <KFILE>;
    close(KFILE)
}

# create lists of things indexed by kinds.
sub split_fields {
    my $kind_cat_bits;
    # matches anything with three whitespace-delimited alphanumeric fields,
    # followed by rest of line.  Automatically ignores lines beginning with '#' and blank lines.
    for (@kindlines) {
	if (/Categories:\s+(.*)/) {
	    @category_names = split(/\s+/, $1);
	    $i = 0;
	    for (@category_names) {
		$cat_index{$_} = $i++;
		# print "cat_index{$_} = $i\n";
	    }
	}
	elsif (/^(\w+)\s+(\w+)\s+(\w+|-)\s+(.*)/) {
	    push(@kindnames, $1);
	    push(@minkids, $2);
	    push(@maxkids, $3);
	    @kind_cats = split(/\s+/, $4);
	    # build a bit vector of categories.
	    $kind_cat_bits = 0;
	    for (@kind_cats) {
		$kind_cat_bits |= (1 << int($cat_index{$_}));
	    }
	    push(@cat_bits, $kind_cat_bits);
	}
    }
}

sub gen_h_file {
    open(HFILE, "> ASTKind.h") || die "Cannot open .h file: $!\n";

    print HFILE
	"// -*- c++ -*-\n",
	"#ifndef TESTKINDS_H\n",
	"#define TESTKINDS_H\n",
	"// Generated automatically by genkinds.pl from ASTKind.kinds $now.\n",
	"// Do not edit\n",
	"#include <iostream>\n",
	"namespace BEEV {\n  typedef enum {\n";

    for my $i (0 .. $#kindnames) {
	print HFILE "    ", $kindnames[$i];
	print HFILE "," unless $i == $#kindnames;
	print HFILE "\n";
    }

    print HFILE
	"} Kind;\n\n",
	"extern unsigned char _kind_categories[];\n\n";

    # For category named "cat", generate functions "bool is_cat_kind(k);"


    for (@category_names) {
	my $catname = $_;
	my $kind_cat_bit = (1 << int($cat_index{$catname}));
	print HFILE "inline bool is_", $catname, "_kind(Kind k) { return (_kind_categories[k] & $kind_cat_bit); }\n\n"
    }

    print HFILE
	"extern const char *_kind_names[];\n\n",
	"/** Prints symbolic name of kind */\n",
	"inline std::ostream& operator<<(std::ostream &os, const Kind &kind) { os << _kind_names[kind]; return os; }\n",
	"\n\n",
	"}  // end namespace\n",
	"\n\n#endif\n";

    close(HFILE);
}

# generate the .cpp file

sub gen_cpp_file {
    open(CPPFILE, "> ASTKind.cpp") || die "Cannot open .h file: $!\n";

    print CPPFILE
	"// Generated automatically by genkinds.h from ASTKind.kinds $now.\n",
	"// Do not edit\n",
	"namespace BEEV {\n",
	"const char * _kind_names[] =  {\n";
    for (@kindnames) {
	print CPPFILE "   \"$_\",\n";
    }
    print CPPFILE "};\n\n";

    # category bits
    print CPPFILE
	"unsigned char _kind_categories[] = {\n";
    for (@cat_bits) {
	print CPPFILE "   $_,\n";
    }
    print CPPFILE
	"};\n",
	"\n}  // end namespace\n";

    close(CPPFILE);
}

&read_kind_defs;
&split_fields;
&gen_h_file;
&gen_cpp_file;
