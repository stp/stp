#!/bin/bash

#######################x
# AUTHORS: Dan Liew
#
# BEGIN DATE: Nov, 2014
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
########################x


# Format headers and source files but avoid external projects
files="$(find include/ -iname '*.h' -o -iname '*.cpp' | sort)"
files="$files $(find lib/ \( -iname '*.h' -o -iname '*.cpp' \) -not \( -path 'lib/extlib-*' -o -path 'lib/Sat/minisat/*' -o -path 'lib/Sat/cryptominisat2/*' \) | sort )"
files="$files $(find tools/ -iname '*.h' -o -iname '*.cpp' | sort)"
files="$files $(find tests/api \( -iname '*.h' -o -iname '*.cpp' -o -iname '*.c' \) | sort)"
for f in $files; do
    echo "Formating $f"
    clang-format -i -style=file $f
done
