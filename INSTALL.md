STP is built with [CMake](http://cmake.org/), version 3.0.2 or newer

CMake is a meta build system that generates build files for other tools such as
make(1), Visual Studio, Xcode, etc.

# Useful configuration variables
Here are a few interesting configuration variables. These apply to all
generators.

- ``CMAKE_BUILD_TYPE`` - The build type (e.g. Release)
- ``CMAKE_INSTALL_PREFIX`` - The prefix for install (e.g. /usr/local )
- ``ENABLE_ASSERTIONS`` - If TRUE STP will be built with asserts.
- ``ENABLE_TESTING`` - Enable running tests
- ``ENABLE_PYTHON_INTERFACE`` - Enable building the Python interface
- ``PYTHON_EXECUTABLE`` - Set python executable in case you have more than one python installed
- ``SANITIZE`` - Use Clang's sanitization checks
- ``STATICCOMPILE`` - Build static libraries and binaries instead of dynamic

# Dependencies
STP relies on : boost, flex, bison and minisat. You can install these by:

```
$ sudo apt-get install cmake bison flex libboost-all-dev python perl
```

Installing minisat:

```
$ git clone https://github.com/niklasso/minisat.git
$ cd minisat
$ mkdir build && cd build
$ cmake ..
$ make
$ sudo make install
$ sudo ldconfig
```

### CryptoMiniSat

STP uses minisat as its SAT solver by default but it also supports other SAT solvers including CryptoMiniSat as an optional extra. If installed, it will be detected during the cmake and used:

```
$ git clone https://github.com/msoos/cryptominisat
$ cd cryptominisat
$ mkdir build && cd build
$ cmake ..
$ make
$ sudo make install
$ sudo ldconfig
```

### Static library and binary

```
$ git clone https://github.com/stp/stp.git
$ cd stp
$ mkdir build && cd build
$ cmake -DSTATICCOMPILE=ON ..
$ make
$ sudo make install
$ sudo ldconfig
```

### Testing

Testing depends on GoogleTest, lit  and Outputcheck:

```
$ git submodule init
$ git submodule update
$ pip install lit
```

# Building

### Quick start
To build STP make sure you have its dependencies installed then run

```
mkdir build && cd build
cd build
cmake ..
make
```

You can also build inside the directory, without creating "build", but it's
more error-prone and not recommended.


### Configuration & Build
```

To tweak the build configuration:

* Run ``cmake-gui /path/to/stp/source/root`` instead of ``cmake``. This
  user interface lets you control the value of various configuration
  variables and lets you pick the build system generator.

* Run ``ccmake`` instead of ``cmake``. This provides an ncurses terminal
  interface for changing configuration variables.

* Pass ``-D<VARIABLE>=<VALUE>`` options to ``cmake`` (not very user friendly).
  It is probably best if you **only** configure this way if you are writing
  scripts.

You can also tweak configuration later by running `make edit_cache` and edit any configuration variables, reconfigure and then regenerate the build system. After configuration, build by running `make`.

You can use the `-j<n>` flag to significantly to decrease build time by running `<n>` jobs in parallel (e.g. `make -j4`).

### Testing (optional)

```
# we are in the source directory
mkdir build
cd build
cmake -DENABLE_TESTING=ON ..
make
make check

```

### Installing

To install run `make install` and to uninstall run `make uninstall`. The root of installation is controlled by the `CMAKE_INSTALL_PREFIX` variable at configure time. You can change this by running `make edit_cache` and editing the value of `CMAKE_INSTALL_PREFIX`.


## Visual Studio

Let's assume you put STP's source into c:\projects\stp and you have cygwin and
git installed. Get zlib:

```
cd C:\projects\stp
git clone https://github.com/madler/zlib
cd zlib
git checkout v1.2.8
echo %cd%
mkdir build
mkdir myinstall
cd build
cmake -G %"Visual Studio 14 2015 Win64"% -DCMAKE_INSTALL_PREFIX=%ZLIB_ROOT% ..
cmake --build . --config %CONFIGURATION%
cmake --build . --config %CONFIGURATION% --target install
dir ..\myinstall\
```

Get minisat:

```
cd C:\projects\stp
git clone https://github.com/msoos/minisat
cd minisat
echo %cd%
mkdir build
mkdir myinstall
cd build
cmake -G %"Visual Studio 14 2015 Win64"% -DCMAKE_INSTALL_PREFIX=%MINISAT_ROOT% -DZLIB_ROOT=%ZLIB_ROOT% ..
cmake --build . --config %CONFIGURATION%
cmake --build . --config %CONFIGURATION% --target install
dir ..\myinstall\
dir ..\myinstall\lib\
dir ..\myinstall\bin\
dir ..\myinstall\include\
```


Get flex, bison, perl:

```
C:\cygwin64\setup-x86_64.exe  -qnNd -R C:/cygwin64 -s http://cygwin.mirror.constant.com -l C:/cygwin64/var/cache/setup --packages "flex,bison,perl"
```

Finally, Build STP:

```
cd c:\projects\stp
git submodule update --init --recursive
mkdir ..\stp.build
cd ..\stp.build
cmake --version
cmake -G %"Visual Studio 14 2015 Win64"% -DBoost_USE_STATIC_LIBS=ON -DENABLE_TESTING=ON -DPYTHON_EXECUTABLE="%PYTHON%\\python.exe" -DPYTHON_LIB_INSTALL_DIR="%PYTHON%" -DLIT_TOOL="%PYTHON%\\Scripts\\lit.exe" -DMINISAT_LIBDIR=%MINISAT_ROOT% -DMINISAT_INCLUDE_DIRS=%MINISAT_ROOT%\include -DZLIB_ROOT=%ZLIB_ROOT% -DCMAKE_PREFIX_PATH=C:\cygwin64 ..\stp
cmake --build . --config %CONFIGURATION%
cmake --build . --config %CONFIGURATION% --target install
```
