#!/bin/bash
set -e
set -x

rm -rf stp* tests tools lib bindings include
rm -rf cmake* CM* Makefile ./*.cmake
CXX=clang++ cmake -DFORCE_CMS=ON  ..
make -j4
make check -j4
