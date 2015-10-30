#!/bin/bash -x
set -e

# AUTHORS: Dan Liew
#
# BEGIN DATE: Jul, 2014
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECT

# This file wraps CMake invocation for TravisCI
# so we can set different configurations via environment variables.
#
# We could modify our CMake scripts to read environment variables directly but
# that would create two ways of setting the same thing which doesn't seem like
# a good idea.

SOURCE_DIR=`pwd`
cd build
BUILD_DIR=`pwd`
COMMON_CMAKE_ARGS="-G \"Unix Makefiles\" -DENABLE_TESTING:BOOL=ON -DLIT_ARGS:STRING=-v"

# Note eval is needed so COMMON_CMAKE_ARGS is expanded properly
case $STP_CONFIG in
    STATIC_LIB)
        eval sudo apt-get install -y libboost-all-dev
        eval cmake ${COMMON_CMAKE_ARGS} \
                   -DBUILD_SHARED_LIBS:BOOL=OFF \
                   -DBUILD_STATIC_BIN:BOOL=OFF \
                   -DENABLE_PYTHON_INTERFACE:BOOL=OFF \
                   ${SOURCE_DIR}
    ;;

    COVERAGE)
        eval sudo apt-get install -y libboost-all-dev
        eval cmake ${COMMON_CMAKE_ARGS} \
                    -DCOVERAGE:BOOL=ON \
                   ${SOURCE_DIR}
    ;;

    INTREE_BUILD)
        cd ..
        SOURCE_DIR="."
        eval sudo apt-get install -y libboost-all-dev
        eval cmake ${COMMON_CMAKE_ARGS} \
                   ${SOURCE_DIR}

    ;;

    DYNAMIC_LIB)
        eval sudo apt-get install -y libboost-all-dev
        eval cmake ${COMMON_CMAKE_ARGS} \
                   -DBUILD_SHARED_LIBS:BOOL=ON \
                   -DBUILD_STATIC_BIN:BOOL=OFF \
                   -DALSO_BUILD_STATIC_LIB:BOOL=OFF \
                   ${SOURCE_DIR}
    ;;

    DYNAMIC_AND_STATIC_LIB)
        eval sudo apt-get install -y libboost-all-dev
        eval cmake ${COMMON_CMAKE_ARGS} \
                   -DBUILD_SHARED_LIBS:BOOL=ON \
                   -DBUILD_STATIC_BIN:BOOL=OFF \
                   -DALSO_BUILD_STATIC_LIB:BOOL=ON \
                   ${SOURCE_DIR}
    ;;

    STATIC_BINARY)
        eval sudo apt-get install -y libboost-all-dev
        eval cmake ${COMMON_CMAKE_ARGS} \
                   -DBUILD_STATIC_BIN:BOOL=ON \
                   -DENABLE_PYTHON_INTERFACE:BOOL=OFF \
                   ${SOURCE_DIR}
    ;;

    RELEASE)
        eval sudo apt-get install -y libboost-all-dev
        eval cmake ${COMMON_CMAKE_ARGS} \
                   -DENABLE_ASSERTIONS:BOOL=OFF \
                   -DCMAKE_BUILD_TYPE:STRING=Release \
                   ${SOURCE_DIR}
    ;;

    KLEE)
        eval sudo apt-get install -y libboost-all-dev
        eval cmake ${COMMON_CMAKE_ARGS} \
                   -DBUILD_SHARED_LIBS:BOOL=OFF \
                   -DENABLE_PYTHON_INTERFACE:BOOL=OFF \
                   ${SOURCE_DIR}
    ;;

    NO_BOOST)
        eval cmake ${COMMON_CMAKE_ARGS} \
                   -DNO_BOOSTS:BOOL=ON \
                   ${SOURCE_DIR}
    ;;

    CPP11)
         eval sudo apt-get install -y libboost-all-dev
         export CC="gcc-4.7"
         export CXX="g++-4.7"
         eval sudo add-apt-repository -y ppa:ubuntu-sdk-team/ppa
         eval sudo add-apt-repository -y ppa:george-edison55/gcc4.7-precise
         eval sudo apt-get update
         eval sudo apt-get install -y gcc-4.7 g++-4.7
         eval cmake ${COMMON_CMAKE_ARGS} \
                   -DBUILD_SHARED_LIBS:BOOL=ON \
                   -DBUILD_STATIC_BIN:BOOL=OFF \
                   -DALSO_BUILD_STATIC_LIB:BOOL=OFF \
                   ${SOURCE_DIR}
    ;;

    *)
        echo "\"${STP_CONFIG}\" configuration not recognised"
        exit 1
esac

make VERBOSE=1
make check

if [ "$STP_CONFIG" = "KLEE" ]; then
    sudo sh -c 'echo "deb http://llvm.org/apt/precise/ llvm-toolchain-precise-3.4 main" >> /etc/apt/sources.list.d/llvm.list'
    sudo sh -c 'echo "deb-src http://llvm.org/apt/precise/ llvm-toolchain-precise-3.4 main" >> /etc/apt/sources.list.d/llvm.list'
    sudo sh -c 'echo "deb http://llvm.org/apt/precise/ llvm-toolchain-precise-3.5 main" >> /etc/apt/sources.list.d/llvm.list'
    sudo sh -c 'echo "deb-src http://llvm.org/apt/precise/ llvm-toolchain-precise-3.5 main" >> /etc/apt/sources.list.d/llvm.list'
    # Needed for new libstdc++ and gcc4.8
    sudo add-apt-repository --yes ppa:ubuntu-toolchain-r/test/
    wget -O - http://llvm.org/apt/llvm-snapshot.gpg.key|sudo apt-key add -
    sudo apt-get update
    sudo apt-get install build-essential curl git bison flex bc libcap-dev git cmake libboost-all-dev libncurses5-dev python-minimal python-pip unzip

    sudo apt-get install gcc-4.8 g++-4.8 libcap-dev cmake
    # Make gcc4.8 the default gcc version
    sudo update-alternatives --install /usr/bin/gcc gcc /usr/bin/gcc-4.8 20
    sudo update-alternatives --install /usr/bin/g++ g++ /usr/bin/g++-4.8 20
    # Make Clang3.4 the default clang version
    sudo apt-get install clang-3.4
    sudo update-alternatives --install /usr/bin/clang clang /usr/bin/clang-3.4 20
    sudo update-alternatives --install /usr/bin/clang++ clang++ /usr/bin/clang++-3.4 20

    # Install LLVM and the LLVM bitcode compiler we require to build KLEE
    LLVM_VERSION=3.4
    STP_VERSION=master
    KLEE_UCLIBC=1
    DISABLE_ASSERTIONS=0
    ENABLE_OPTIMIZED=1
    COVERAGE=0
    sudo apt-get install llvm-${LLVM_VERSION} llvm-${LLVM_VERSION}-dev
    KLEE_CC=/usr/bin/clang-${LLVM_VERSION}
    KLEE_CXX=/usr/bin/clang++-${LLVM_VERSION}

    #build klee-uclibc
    git clone --depth 1 git://github.com/klee/klee-uclibc.git
    cd klee-uclibc
    ./configure --make-llvm-lib --with-cc "${KLEE_CC}" --with-llvm-config /usr/bin/llvm-config-${LLVM_VERSION}
    make
    KLEE_UCLIBC_CONFIGURE_OPTION="--with-uclibc=$(pwd) --enable-posix-runtime"
    cd ../

    #klee
    wget https://github.com/klee/klee/archive/v1.0.0.tar.gz
    tar xzvf v1.0.0.tar.gz
    cd klee-1.0.0
    ./configure --with-llvmsrc=/usr/lib/llvm-${LLVM_VERSION}/build \
        --with-llvmobj=/usr/lib/llvm-${LLVM_VERSION}/build \
        --with-llvmcc=${KLEE_CC} \
        --with-llvmcxx=${KLEE_CXX} \
        --with-stp="${BUILD_DIR}" \
        ${KLEE_UCLIBC_CONFIGURE_OPTION} \
        CXXFLAGS="${COVERAGE_FLAGS}"

    make DISABLE_ASSERTIONS=${DISABLE_ASSERTIONS} \
        ENABLE_OPTIMIZED=${ENABLE_OPTIMIZED} \
        ENABLE_SHARED=0

    cd ${BUILD_DIR}
fi

# Build example project. We assume that the build installed itself to the CMake
#- mkdir simple_example
#- cd simple_example
#- cmake -G "Unix Makefiles" -DUSE_STP_SHARED_LIBRARY=$( test -f ../stp/lib/libstp.so && echo ON || echo OFF) ../../examples/simple
#- make VERBOSE=1
#- ./stp-example

if [ "$STP_CONFIG" = "COVERAGE" ]; then
    cd ..

    # capture coverage info
    lcov --directory  build/lib/ --capture --output-file coverage.info

    # filter out system and test code
    lcov --remove coverage.info 'tests/*' '/usr/*' --output-file coverage.info

    # debug before upload
    lcov --list coverage.info
    coveralls-lcov --repo-token $COVERTOKEN coverage.info # uploads to coveralls

    exit 0
fi

if [ "$STP_CONFIG" != "NO_BOOST" ] && [ "$STP_CONFIG" != "INTREE_BUILD" ] ; then
    cd ../..

    #
    # get fuzzsmt
    sudo apt-get install -y default-jre
    git clone --depth 1 https://github.com/msoos/fuzzsmt.git

    #lingeling
    git clone https://github.com/msoos/lingeling-ala lingeling
    cd lingeling
    ./configure
    make
    sudo cp lingeling /usr/bin/
    cd ..

    # get boolector
    git clone --depth 1 https://github.com/msoos/boolector-1.5.118.git
    cd boolector-1.5.118
    ./configure
    make
    sudo cp boolector /usr/bin/
    cd ..

    #fuzz
    cd stp/scripts/
    ./fuzz_test.py -n 20 --novalgrind

    #test install
    cd ../build/
    sudo make install
fi

exit 0
