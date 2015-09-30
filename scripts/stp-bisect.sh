#!/usr/bin/env bash

# Copyright (c) 2015 Ryan Govostes
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
#

# This script is a template to use when performing a git-bisect(1) on the STP
# codebase. Duplicate this file outside of the source tree before modifying it.
#
# Revisions which do not build will be skipped.
#
# Tests will be run when possible. Revisions which fail tests will be skipped.
# List test targets in thes TESTS array. 'check' will run all of them.
#
# Example usage:
#   git bisect start 04256f9 e8703fb
#   git bisect run /tmp/stp-bisect.sh


BUILDDIR=/tmp/stpbisect
SRCDIR="$(pwd)"

# Clean untracked files that might have been left behind
git clean --force -d

# Build
rm -Rf "$BUILDDIR" && mkdir "$BUILDDIR" && cd "$BUILDDIR"
cmake -G "Unix Makefiles" -DENABLE_TESTING=1 "$SRCDIR"
if [ "$?" -ne "0" ]; then
  # Might have failed to enable testing, try again
  rm -f CMakeCache.txt
  cmake -G "Unix Makefiles" "$SRCDIR" || exit 125
fi
make || exit 125

# Run tests
TESTS=( query-file-tests )
for TEST in "${TESTS[@]}"; do
  make --dry-run "$TEST"
  if [ "$?" -ne "2" ]; then
    make "$TEST" || exit 125
  fi
done

# Invoke STP
# Use grep(1) to determine whether the query was satisfiable.
./stp /dev/stdin <<EOF | grep -q 'Valid.'
  X : BITVECTOR(31);
  Y : BITVECTOR(31);
  QUERY (
  LET NODE134 =
  (BVPLUS(32,0bin00000000000000000000000000000001[31:0],(0bin0@Y)[31:0])) IN (
  LET NODE136 = (SBVLT(NODE134[31:0],
  0bin00000000000000000000000000000000[31:0])) IN (
  LET NODE137 = (NOT(NODE136)) IN (
  LET NODE212 = (SBVLT((0bin0@Y)[31:0], (0bin0@X)[31:0])) IN (
  LET NODE213 = (NOT(NODE212)) IN (
  LET NODE214 = (SBVLT((0bin0@X)[31:0], (0bin0@Y)[31:0])) IN (
  (NODE214 OR NODE213 OR NODE137))))))));
EOF

# Return 0 to indicate that this revision is good, 1 for bad.
if [ "$?" -eq "0" ]; then
  exit 0
else
  exit 1
fi
