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

# give the package a unique name
DESCRIPTION=$(git rev-parse --short HEAD)

# make sure we clean up
trap 'rm -rf $TMPD' EXIT
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
sudo make install
cd ..

git clone --depth 1 https://github.com/msoos/cryptominisat.git
cd cryptominisat
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
make r -j $(nproc)
echo "Minisat: $(git rev-parse --short HEAD)" >> ../COMMITS
cd ..
cp minisat/build/release/bin/minisat bin

# Riss
git clone --depth 1 https://github.com/conp-solutions/riss.git
cd riss
echo "Riss: $(git rev-parse --short HEAD)" >> ../COMMITS
mkdir -p build
cd build
cmake .. -DDRATPROOF=OFF -DCMAKE_BUILD_TYPE=Release
make riss-core -j $(nproc)
cd ../..
cp riss/build/bin/riss-core bin/riss

# build STP
mkdir -p stp-build
cd stp-build
cmake -DSTATICCOMPILE:BOOL=ON \
 -DENABLE_ASSERTIONS:BOOL=OFF \
 -DCMAKE_BUILD_TYPE:STRING=Release \
 ../stp
make -j $(nproc)
cd ..
cp stp-build/stp-2.1.2 bin

# Cleanup solver directories
rm -rf stp-build minisat m4ri-20140914 cryptominisat riss stp ./*.tar.gz

# Get rid of extra symbols in solvers
cd bin
strip ./* || true
cd ..

# compress
zip -r -9 stp.zip ./*

# jump back and move stp.zip here, giving it a full name
popd
mv "$TMPD"/stp.zip ./stp-"$DESCRIPTION".zip
