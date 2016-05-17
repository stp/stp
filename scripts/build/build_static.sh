#!/bin/bash
set -e
set -x

rm -rf stp* tests tools lib bindings include
rm -rf cmake* CM* Makefile ./*.cmake
cmake -DENABLE_TESTING=ON -DBUILD_STATIC_BIN=ON -DCMAKE_BUILD_TYPE=Release -DBUILD_SHARED_LIBS=OFF -DFORCE_CMS=ON   ..
make -j4 VERBOSE=1
