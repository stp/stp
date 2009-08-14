#!/bin/sh
PREFIX=$HOME

while [ $# -gt 0 ]; do
    case "$1" in
	--with-prefix=*)
	    arg=`expr "x$1" : 'x[^=]*=\(.*\)'`
	    PREFIX=$arg;;
	*)
	    echo "Usage: ./clean-install [options]"
	    echo "   --with-prefix=/prefix/path   Installs STP at the specified path"
	    echo "configure failed"
	    exit 1;;
    esac

    shift
done


./scripts/configure --with-prefix=$PREFIX
make clean
make
make install

