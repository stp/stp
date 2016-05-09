#!/bin/bash
set -ex


rm -rf bindings
rm -rf CM*
rm -rf tests
rm -rf stp*
cmake -DENABLE_TESTING=ON ..
make -j4
make check
echo "ALL IS OK"
