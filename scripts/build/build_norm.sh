#!/bin/bash
set -e
set -x

rm -rf stp* tests tools lib bindings include
rm -rf cmake* CM* Makefile ./*.cmake
cmake -DFORCE_CMS=ON -DENABLE_TESTING=ON ..
make -j4
