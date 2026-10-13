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

# Build STP.
#
# --auto-download supplies every dependency: CryptoMiniSat, MiniSat, CaDiCaL,
# LibBF, ABC, SymFPU, CLI11 and the rest, each at the revision its
# cmake/Find*.cmake pins and with the flags it builds it with -- the
# combination CI exercises, with one pin per dependency to move. That is why
# git and ca-certificates are in the package list, and it is also what makes
# MiniSat build at all -- 2.2.1 declares cmake_minimum_required(VERSION 2.6),
# which the CMake on this base image refuses, and cmake/deps-helper.cmake
# passes the -DCMAKE_POLICY_VERSION_MINIMUM that gets it through. Building it
# by hand here, outside that, did not.
#
# CryptoMiniSat needs GMP, which STP cannot build, and looks it up through
# pkg-config, which is why libgmp-dev and pkg-config are in the package list
# too.
#
# All three backends are named explicitly rather than left to whatever is
# installed. They fit in one static binary without accommodation: STP builds
# CryptoMiniSat -DNOCADICAL=ON, so it brings no CaDiCaL of its own, and the
# CaDiCaL linked is the one STP pins.
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
