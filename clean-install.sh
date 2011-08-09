#!/bin/sh
if [ "$PREFIX" == "" ]; then
	PREFIX=$HOME
fi

make configclean
. scripts/configure
make clean
make install

