#!/bin/bash
set -e
set -x

rm -rf stp* tests tools lib bindings include
rm -rf cmake* CM* Makefile ./*.cmake
cmake -DSTATICCOMPILE=ON -DFORCE_CMS=ON   ..
make -j4 VERBOSE=1
