FROM ubuntu:16.04 as builder

LABEL maintainer="Mate Soos"
LABEL version="5.0"
LABEL Description="An advanced SAT solver"

# get curl, etc
RUN apt-get update && apt-get install --no-install-recommends -y software-properties-common && rm -rf /var/lib/apt/lists/*
RUN add-apt-repository -y ppa:ubuntu-toolchain-r/test && rm -rf /var/lib/apt/lists/*
RUN apt-get update && apt-get install --no-install-recommends -y libboost-program-options-dev gcc g++ make cmake zlib1g-dev wget && rm -rf /var/lib/apt/lists/*
RUN apt-get update && apt-get install --no-install-recommends -y bison flex \
    && rm -rf /var/lib/apt/lists/*

# get M4RI
RUN mkdir /m4ri-20140914
WORKDIR /m4ri-20140914
RUN wget https://bitbucket.org/malb/m4ri/downloads/m4ri-20140914.tar.gz \
    && tar -xvf m4ri-20140914.tar.gz
WORKDIR /m4ri-20140914/m4ri-20140914
RUN ./configure
RUN make -j6
RUN make install
RUN make clean

# build CMS
RUN mkdir /cms
WORKDIR /cms
RUN wget -O cryptominisat.tgz https://github.com/msoos/cryptominisat/archive/5.6.5.tar.gz
RUN tar xvf cryptominisat.tgz --strip-components 1
RUN mkdir build
WORKDIR /cms/build
RUN cmake -DSTATICCOMPILE=ON ..
RUN make -j6
RUN make install

RUN mkdir /minisat
WORKDIR /minisat
RUN wget -O minisat.tgz https://github.com/stp/minisat/archive/releases/2.2.1.tar.gz
RUN tar xvf minisat.tgz --strip-components 1
RUN mkdir build
WORKDIR /minisat/build
RUN cmake ..
RUN make -j6
RUN make install

# build stp
RUN mkdir /stp
WORKDIR /stp
COPY . /stp
RUN mkdir build
WORKDIR /stp/build
RUN cmake -DSTATICCOMPILE=ON ..
RUN make -j6
RUN make install

# set up for running
# set up for running
FROM alpine:latest
COPY --from=builder /usr/local/bin/stp-2.1.2 /usr/local/bin/
ENTRYPOINT ["/usr/local/bin/stp-2.1.2", "--SMTLIB2"]

# --------------------
# HOW TO USE
# --------------------
# on file through STDIN:
#    cat myfile.smt | docker run --rm -i -a stdin -a stdout stp


