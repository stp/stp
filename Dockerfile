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

# Build CryptoMiniSat, at the commit cmake/FindCryptoMiniSat.cmake pins and
# with the flags it uses -- that is the combination CI exercises. Built here
# rather than left to the build's own ExternalProject so that this stage is
# cached separately from the STP compile below.
#
# BUILD_SHARED_LIBS=OFF rather than STATICCOMPILE=ON: 5.14 removed
# STATICCOMPILE, and BUILD_SHARED_LIBS defaults to ON, so asking the old way
# now yields a shared libcryptominisat5 that the scratch image below cannot
# carry. STATIC_BINARY=OFF because only the library is wanted here; a fully
# static cryptominisat5 executable would need static gmp and zlib.
#
# NOCADICAL=ON, so 5.14 fetches and builds neither CaDiCaL nor cadiback: STP
# reaches backbone extraction, the only thing CryptoMiniSat wants CaDiCaL for,
# from nowhere. git and ca-certificates are still needed for the clone itself,
# and GMP is looked up through pkg-config, which is why that is in the package
# list above.
WORKDIR /cms
RUN git clone https://github.com/stp/cryptominisat . \
 && git checkout 261392c4e993f40638392012b689a0a4a7794355 \
 && mkdir build && cd build \
 && cmake .. \
        -DCMAKE_BUILD_TYPE=Release \
        -DENABLE_ASSERTIONS=OFF \
        -DBUILD_SHARED_LIBS=OFF \
        -DSTATIC_BINARY=OFF \
        -DNOCADICAL=ON \
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
# All three backends are named explicitly rather than left to whatever is
# installed. CaDiCaL is the subtle one: CryptoMiniSat 5.14 builds and installs
# its own, so with a static libcryptominisat5 -- which is what a scratch image
# needs -- both archives would reach libstp's link line and their symbols
# would collide. The guard in the top-level CMakeLists refuses that, with one
# exception: if STP resolves CaDiCaL to the same archive CryptoMiniSat
# installed, there is only one library and one set of symbols. That is what
# happens here, because rung 1 of cmake/FindCaDiCaL.cmake searches the system
# prefixes and CryptoMiniSat put cadical/cadical.hpp and libcadical.a in
# /usr/local above. Configure prints which copy it settled on.
#
# The cost is that CaDiCaL is then whatever CryptoMiniSat bundles rather than
# the newer revision STP pins for itself, so --cadical-factor detects the older
# version and turns itself off. Building CryptoMiniSat shared would avoid that,
# but a scratch image cannot carry the .so.
WORKDIR /stp
COPY . /stp
RUN cmake -S . -B build \
        -DCMAKE_BUILD_TYPE=Release \
        -DENABLE_ASSERTIONS=OFF \
        -DSTATICCOMPILE=ON \
        -DENABLE_AUTO_DOWNLOAD=ON \
        -DUSE_CRYPTOMINISAT=ON \
        -DUSE_MINISAT=ON \
        -DUSE_CADICAL=ON \
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
