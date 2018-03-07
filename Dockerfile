FROM msoos/cryptominisat:latest

LABEL maintainer="Mate Soos"
LABEL version="1.0"
LABEL Description="An advanced SMT solver"

# get curl, etc
USER root
RUN apt-get update && apt-get install --no-install-recommends -y bison flex \
    && rm -rf /var/lib/apt/lists/*

# get M4RI
# RUN wget https://bitbucket.org/malb/m4ri/downloads/m4ri-20140914.tar.gz \
#     && tar -xvf m4ri-20140914.tar.gz
# WORKDIR m4ri-20140914
# RUN ./configure \
#     && make \
#     && make install \
#     && make clean

# build minisat
RUN mkdir -p /home/solver/
WORKDIR /home/solver/
RUN wget https://github.com/stp/minisat/archive/releases/2.2.1.tar.gz \
    && tar xvf 2.2.1.tar.gz
WORKDIR /home/solver/minisat-2.2.1/
RUN mkdir build && cd build && cmake .. \
    && make -j6 \
    && make install \
    && cd .. \
    && rm -rf build


# build stp
COPY . /home/solver/stp
WORKDIR /home/solver/stp
RUN mkdir build
WORKDIR /home/solver/stp/build
RUN cmake .. \
    && make -j6 \
    && make install \
    && rm -rf *

# set up for running
USER solver
WORKDIR /home/solver/
ENTRYPOINT ["stp", "--SMTLIB2"]

# --------------------
# HOW TO USE
# --------------------
# on file through STDIN:
#    cat myfile.smt | docker run --rm -i -a stdin -a stdout stp


