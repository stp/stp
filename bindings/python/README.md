# STP's Python API

The Python API of [STP](https://github.com/stp/stp): the `stp` package, a
z3py-style shell over the compiled module `stp._core`, which calls STP's C API
(`<stp/stp.h>`). `docs/api3.rst` in the STP tree is the guide to it.

## Two ways to install it

**With STP's CMake build.** Configure STP with `-DENABLE_PYTHON_API=ON` (the
default when the interpreter can import Cython), and `cmake --install`
installs the package under the install prefix. `PYTHON_LIB_INSTALL_DIR`
chooses the directory, relative to the prefix unless it is absolute.

**With pip, against an STP that is already installed.** Install STP first (a
shared-library build, the default), then, once per Python interpreter:

    python3 -m pip install ./bindings/python

This compiles the package's extension against the installed STP, so it needs
a C compiler and the interpreter's development headers; pip fetches Cython.
It is how to give several Python versions the API of one installed `libstp`.
It is not supported on Windows, where the CMake build is the way.

## Finding the installation

pip looks for STP's headers and its shared `libstp` under:

1. `STP_PREFIX`, if set, and nothing else;
2. otherwise the prefix of the `stp` on `PATH`, then `/usr/local`, then `/usr`.

The headers are `include/stp/stp.h` and the generated sources the install
puts in `include/stp/api/python` for this build; the library is looked for in
`lib64` and then `lib`. `STP_INCLUDE_DIR` and `STP_LIBRARY_DIR` name the two
directories outright, for an installation laid out otherwise.

The extension records the library directory it was built against as its
rpath, so `import stp` loads that `libstp` with nothing set. The generated
sources come from the same tables as that library, so build against the STP
you are going to run.

## Example

    from stp import *

    x, y = BitVecs('x y', 32)
    s = Solver()
    s.add(ULT(x + y, 20), UGT(x, 10), UGT(y, 10))
    print(s.check())  # sat
    print(s.model())  # e.g. [x = 4294967288, y = 11]
