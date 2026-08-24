# This Dockerfile builds a statically-compiled instance of STP with MiniSat and
# CryptoMiniSat that evaluates SMTLIB2 inputs provided on standard input:
#
#     docker build --tag stp/stp .
#     cat example.smt2 | docker run --rm -i stp/stp


FROM ubuntu:24.04 AS builder

# Install dependencies
RUN apt-get update \
 && apt-get install --no-install-recommends -y \
        bison \
        ca-certificates \
        cmake \
        flex \
        g++ \
        gcc \
        git \
        libgmp-dev \
        libm4ri-dev \
        libncurses-dev \
        make \
        python3 \
        wget \
        zlib1g-dev \
 && rm -rf /var/lib/apt/lists/*

# Build CMS
WORKDIR /cms
RUN wget -O cryptominisat.tgz https://github.com/msoos/cryptominisat/archive/5.11.21.tar.gz \
 && tar xvf cryptominisat.tgz --strip-components 1 \
 && mkdir build && cd build \
 && cmake .. \
        -DCMAKE_BUILD_TYPE=Release \
        -DENABLE_ASSERTIONS=OFF \
        -DSTATICCOMPILE=ON \
 && cmake --build . \
 && cmake --install .

# Build MiniSat
WORKDIR /minisat
RUN wget -O minisat.tgz https://github.com/stp/minisat/archive/releases/2.2.1.tar.gz \
 && tar xvf minisat.tgz --strip-components 1 \
 && mkdir build && cd build \
 && cmake .. \
        -DCMAKE_BUILD_TYPE=Release \
 && cmake --build . \
 && cmake --install .

# Build STP.
#
# --auto-download supplies LibBF, which is required and which nothing above
# builds -- this image could not have built at all without a deps/libbf that
# happened to be sitting in the build context. git and ca-certificates are in
# the package list above for its sake.
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
