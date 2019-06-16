#!/usr/bin/env bash
#
# Copyright (c) 2018 Norbert Manthey
#
# This script creates a package for starexec, including statically linked
# third-party SAT solvers
#
# The script will install m4ri on the system from source.

# make sure we notice failures early
set -e -x

# make sure we know where the code is
SOLVERDIR=$(pwd)
BRANCH=$(git rev-parse --abbrev-ref HEAD)

if [ ! -x "$SOLVERDIR"/scripts/make-starexec.sh ]
then
	echo "Error: script has to be called from base directory, abort!"
	exit 1
fi

# check for being on a branch
if [ -z "$BRANCH" ]
then
	echo "Error: failed to extract a git branch, abort!"
	exit 1
fi

# shall we leave the directory behind?
NO_CLEANUP=${NO_STP_CLEANUP:-}

CMSCOMMIT=""
MERGESATCOMMIT=""
MINISATCOMMIT=""
RISSCOMMIT=""
# do we want to package Riss(for Coprocessor) or Sparrow as well?
while getopts "c:g:m:r:" OPTION; do
    case $OPTION in
    c)
        CMSCOMMIT="$OPTARG"
        ;;
    g)
        MERGESATCOMMIT="$OPTARG"
        ;;
    m)
        MINISATCOMMIT="$OPTARG"
        ;;
    r)
        RISSCOMMIT="$OPTARG"
        ;;
    *)
        echo "Unknown options provided"
        ;;
    esac
done

# give the package a unique name
DESCRIPTION=$(git rev-parse --short HEAD)

# make sure we clean up
[ -n "$NO_CLEANUP" ] || trap 'rm -rf $TMPD' EXIT
TMPD=$(mktemp -d)

# create the project directory
pushd "$TMPD"

# copy template
cp -r "$SOLVERDIR"/scripts/starexec/* .

# copy actual source by using the git tree, only the current branch
git clone "$SOLVERDIR" --branch "$BRANCH" --single-branch stp
pushd stp
git checkout "$BRANCH"
git gc
git prune
echo "STP: $(git rev-parse --short HEAD)" >> ../COMMITS
popd

# build SAT solvers
# CryptoMinisat
wget https://bitbucket.org/malb/m4ri/downloads/m4ri-20140914.tar.gz
tar xzvf m4ri-20140914.tar.gz
cd m4ri-20140914/
./configure
make -j $(nproc)
echo "Before proceeding, make sure you want to install m4ri version 20140914 from source"
sleep 5
timeout 10 sudo make install || true
cd ..

git clone --depth 1 https://github.com/msoos/cryptominisat.git
cd cryptominisat
[ -z "$CMSCOMMIT" ] || git checkout -b stp-build "$CMSCOMMIT"
echo "CryptoMinisat: $(git rev-parse --short HEAD)" >> ../COMMITS
mkdir build
cd build
cmake -DREQUIRE_M4RI=ON -DSTATICCOMPILE=ON -DENABLE_PYTHON_INTERFACE=OFF -DNOVALGRIND=ON -DCMAKE_BUILD_TYPE=Release ..
make -j $(nproc)
cd ../..
cp cryptominisat/build/cryptominisat5 bin

# Minisat
git clone --depth 1 https://github.com/niklasso/minisat.git
cd minisat
[ -z "$MINISATCOMMIT" ] || git checkout -b stp-build "$MINISATCOMMIT"
make r -j $(nproc)
echo "Minisat: $(git rev-parse --short HEAD)" >> ../COMMITS
cd ..
cp minisat/build/release/bin/minisat bin

# Riss
git clone --depth 1 https://github.com/conp-solutions/riss.git
cd riss
[ -z "$RISSCOMMIT" ] || git checkout -b stp-build "$RISSCOMMIT"
echo "Riss: $(git rev-parse --short HEAD)" >> ../COMMITS
mkdir -p build
cd build
cmake .. -DDRATPROOF=OFF -DCMAKE_BUILD_TYPE=Release
make riss-core -j $(nproc)
cd ../..
cp riss/build/bin/riss-core bin/riss

# MergeSAT
git clone --depth 1 https://github.com/conp-solutions/mergesat.git
cd mergesat
[ -z "$MERGESATCOMMIT" ] || git checkout -b stp-build "$MERGESATCOMMIT"
echo "MergeSAT: $(git rev-parse --short HEAD)" >> ../COMMITS
make r -j $(nproc) RELEASE_LDFLAGS=-static
cd ..
cp mergesat/build/release/bin/mergesat bin/mergesat

# build STP
mkdir -p stp-build
cd stp-build
cmake -DSTATICCOMPILE:BOOL=ON \
 -DENABLE_ASSERTIONS:BOOL=OFF \
 -DCMAKE_BUILD_TYPE:STRING=Release \
 ../stp
make -j $(nproc)
cd ..
cp stp-build/stp bin

# Cleanup solver directories
[ -n "$NO_CLEANUP" ] || rm -rf stp-build minisat m4ri-20140914 cryptominisat riss stp mergesat ./*.tar.gz

# Get rid of extra symbols in solvers
cd bin
strip ./* || true
cd ..

# compress
zip -r -9 stp.zip ./*

# check binaries for being static

DYNAMIC_BINARIES=$(file bin/* | grep ELF | grep dynamic || true)
if [ -n "$DYNAMIC_BINARIES" ]
then
	echo "Warning, found dynamic binary: $DYNAMIC_BINARIES"
fi

# jump back and move stp.zip here, giving it a full name
popd
mv "$TMPD"/stp.zip ./stp-"$DESCRIPTION".zip
