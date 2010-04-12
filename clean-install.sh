#!/bin/sh
PREFIX=$HOME

make configclean
. scripts/configure
make clean
make install

