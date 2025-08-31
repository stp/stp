# This Dockerfile builds a statically-compiled instance of STP with MiniSat and
# CryptoMiniSat that evaluates SMTLIB2 inputs provided on standard input:
#
#     docker build --tag stp/stp .
#     cat example.smt2 | docker run --rm -i stp/stp


FROM ubuntu:22.04 AS builder

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
        libboost-program-options-dev \
        libgmp-dev \
        libm4ri-dev \
        libtinfo-dev \
        make \
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

# Build STP
COPY . /stp
WORKDIR /stp
RUN ./scripts/deps/setup-kissat.sh
WORKDIR /stp/build
RUN cmake .. \
        -DCMAKE_BUILD_TYPE=Release \
        -DENABLE_ASSERTIONS=OFF \
        -DSTATICCOMPILE=ON \
 && cmake --build . \
 && cmake --install .

# Set up to run in a minimal container
FROM scratch
COPY --from=builder /usr/local/bin/stp /stp
ENTRYPOINT ["/stp", "--SMTLIB2"]
