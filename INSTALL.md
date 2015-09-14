STP is built with [CMake](http://cmake.org/), version 2.8.8 or newer.

CMake is a meta build system that generates build files for other tools such as
make(1), Visual Studio, Xcode, etc. For a list of generators supported on your
platform, consult `cmake --help`.

# Useful configuration variables
Here are a few interesting configuration variables. These apply to all
generators.

- ``BUILD_SHARED_LIBS`` - Build shared libraries rather than static
- ``CMAKE_BUILD_TYPE`` - The build type (e.g. Release)
- ``CMAKE_INSTALL_PREFIX`` - The prefix for install (e.g. /usr/local )
- ``ENABLE_ASSERTIONS`` - If TRUE STP will be built with asserts.
- ``ENABLE_TESTING`` - Enable running tests
- ``ENABLE_PYTHON_INTERFACE`` - Enable building the Python interface
- ``SANITIZE`` - Use Clang's sanitization checks
- ``NO_BOOST`` - Build without using the Boost library
- ``TEST_QUERY_FILES`` -  Test STP externally by passing it query files in tests/query-files
- ``TUNE_NATIVE`` - Tune compilation to native architecture

# Dependencies

STP relies on a few dependencies, namely boost, flex/bison and minisat. Installing
the required header files and binaries can be achieved through the following.
(Tested on Ubuntu 14.04.)

```
$ sudo apt-get install cmake bison flex libboost-all-dev python perl
```

Installing minisat can be achieved by running

```
$ git clone https://github.com/stp/minisat.git
$ cd minisat
$ mkdir build && cd build
$ cmake ..
$ make
$ sudo make install
$ sudo ldconfig
```

### Cryptominisat4

STP uses minisat as its SAT solver by default but it also supports other SAT solvers including Cryptominisat4 as an optional extra. If it is installed it will be detected during the CMake configure and will be available for use in ``stp``.

You can get it from https://github.com/msoos/cryptominisat

### Testing

Testing is optional. STP's testing depends on [GoogleTest][1], [lit][2] and [OutputCheck][3]. To obtain these run

```
$ git submodule init
$ git submodule update
$ pip install lit
```

[1]: https://code.google.com/p/googletest/
[2]: https://pypi.python.org/pypi/lit
[3]: https://github.com/stp/OutputCheck


# Building

### Quick start
To build STP make sure you have its dependencies installed then run

```
$ mkdir build && cd build
$ cmake -G 'Unix Makefiles' /path/to/stp/source/root
$ make
```

If you'd prefer a more in-depth explanation of how to configure, build
test and install STP read on...

### Build directory

CMake supports building in and out of source. It is recommended that
you build out of source. For example in a directory outside of the
STP root source directory run

```
$ mkdir build
```

### Configuration & Build

The simplest thing you can do is use the default configuration by running

```
$ cd build/
$ cmake -G 'Unix Makefiles' /path/to/stp/source/root
```

You can easily tweak the build configuration in several ways

* Run ``cmake-gui /path/to/stp/source/root`` instead of ``cmake``. This
  user interface lets you control the value of various configuration
  variables and lets you pick the build system generator.

* Run ``ccmake`` instead of ``cmake``. This provides an ncurses terminal
  interface for changing configuration variables.

* Pass ``-D<VARIABLE>=<VALUE>`` options to ``cmake`` (not very user friendly).
  It is probably best if you **only** configure this way if you are writing
  scripts.

You can also tweak configuration later by running `make edit_cache`. Then edit any configuration variables, reconfigure and then regenerate the build system. After configuration you can build by running `make`.

Remember you can use the `-j<n>` flag to significantly to decrease build time by running `<n>` jobs in parallel (e.g. `make -j4`).

### Testing (optional)

To run the tests (CMake must of been configured to enable testing) run `make check`. See http://stp.github.io/testing/ for more information on testing.

### Install (optional)

STP and its library can be used directly from the build directory but it can be installed if desired.


To install run `make install` and to uninstall run `make uninstall`. The root of installation is controlled by the ``CMAKE_INSTALL_PREFIX`` variable at configure time. Remember you can easily change this at anytime by running `make edit_cache` and editing the value of ``CMAKE_INSTALL_PREFIX``.

## Ninja

[Ninja](http://martine.github.io/ninja/) is a fast alternative to the ``make``. CMake has support
for it. To use it you need to run

### Quick start

To build STP make sure you have its dependencies installed then run

```
$ mkdir build && cd build
$ cmake -G 'Ninja' /path/to/stp/source/root
$ ninja
```

### More in depth

The instructions are identical to that of the "Using Make" section except that you

* Instruct CMake to use ninja instead of unix make files.
* Use ``ninja`` instead of ``make`` command
* Specifying ``-j`` is not needed. Ninja tries to guess how many jobs to run in parallel.

## Visual Studio

TODO
