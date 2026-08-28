# This Dockerfile builds a statically-compiled instance of STP with MiniSat and
# CryptoMiniSat that evaluates SMTLIB2 inputs provided on standard input:
#
#     docker build --tag stp/stp .
#     cat example.smt2 | docker run --rm -i stp/stp
#
# The base image only has to build STP; what it produces is a static binary on
# scratch, which carries no distribution with it and so runs anywhere. There
# used to be Docker.ubuntu22 and Docker.ubuntu24 alongside this file, differing
# in nothing but this line, and neither had been built by anything.


FROM ubuntu:26.04 AS builder

# Install dependencies
RUN apt-get update \
 && apt-get install --no-install-recommends -y \
        bison \
        ca-certificates \
        cmake \
        flex \
        g++ \
        git \
        libgmp-dev \
        make \
        pkg-config \
        python3 \
        zlib1g-dev \
 && rm -rf /var/lib/apt/lists/*

# Build CryptoMiniSat, at the release scripts/deps/setup-cms.sh pins and with
# the flags it uses -- that is the combination CI exercises.
#
# BUILD_SHARED_LIBS=OFF rather than STATICCOMPILE=ON: 5.14 removed
# STATICCOMPILE, and BUILD_SHARED_LIBS defaults to ON, so asking the old way
# now yields a shared libcryptominisat5 that the scratch image below cannot
# carry. STATIC_BINARY=OFF because only the library is wanted here; a fully
# static cryptominisat5 executable would need static gmp and zlib.
#
# 5.14 fetches and builds its own CaDiCaL and cadiback, which is why git and
# ca-certificates matter to this stage too, and it looks GMP up through
# pkg-config, which is why that is in the package list. Its CaDiCaL is not a
# second copy: USE_CADICAL is off below, so this image has exactly one.
WORKDIR /cms
RUN git clone --depth 1 --branch release/v5.14.7 \
        https://github.com/msoos/cryptominisat . \
 && mkdir build && cd build \
 && cmake .. \
        -DCMAKE_BUILD_TYPE=Release \
        -DENABLE_ASSERTIONS=OFF \
        -DBUILD_SHARED_LIBS=OFF \
        -DSTATIC_BINARY=OFF \
 && cmake --build . \
 && cmake --install .

# Build STP.
#
# --auto-download supplies everything not built above: MiniSat, LibBF, ABC,
# SymFPU, CLI11 and the rest. That is why git and ca-certificates are in the
# package list, and it is also what makes MiniSat build at all -- 2.2.1
# declares cmake_minimum_required(VERSION 2.6), which the CMake on this base
# image refuses, and cmake/deps-helper.cmake passes the
# -DCMAKE_POLICY_VERSION_MINIMUM that gets it through. Building it by hand
# here, outside that, did not.
#
# CryptoMiniSat is built above because it is the one dependency
# --auto-download does not cover.
#
# The two solvers are named explicitly rather than left to whatever is
# installed, and CaDiCaL is turned off: it is on by default, and this image
# links CryptoMiniSat and MiniSat instead.
WORKDIR /stp
COPY . /stp
RUN cmake -S . -B build \
        -DCMAKE_BUILD_TYPE=Release \
        -DENABLE_ASSERTIONS=OFF \
        -DSTATICCOMPILE=ON \
        -DENABLE_AUTO_DOWNLOAD=ON \
        -DUSE_CRYPTOMINISAT=ON \
        -DUSE_MINISAT=ON \
        -DUSE_CADICAL=OFF \
 && cmake --build build \
 && cmake --install build

# Set up to run in a minimal container
FROM scratch
COPY --from=builder /usr/local/bin/stp /stp
# The image is a single static binary on scratch, so these are the only place
# the notices of the code linked into it can live. MIT and BSD components
# require them to accompany the binary; `cmake --install` put them here.
COPY --from=builder /usr/local/share/doc/STP/ /share/doc/STP/
ENTRYPOINT ["/stp", "--SMTLIB2"]
