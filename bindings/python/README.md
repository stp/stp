# STP Python bindings

Python bindings for [STP](https://github.com/stp/stp). They are pure Python
and load the `libstp` shared library through `ctypes`, so one copy of the
package works under every Python 3 and nothing needs compiling.

## Two ways to install them

**With STP's CMake build.** Configure STP with `-DENABLE_PYTHON_INTERFACE=ON`
(the default for a shared-library build), and `cmake --install`
installs the package under the install prefix, recording where it put the
library. `PYTHON_LIB_INSTALL_DIR` chooses the directory.

**With pip, against an STP that is already installed.** Install STP first
(a shared-library build, the default), then, once per Python interpreter:

    python3 -m pip install ./bindings/python

This installs only the Python package. It is how to give several Python
versions the bindings for one installed `libstp`.

## Finding libstp

At import, the package tries, in order:

1. `STP_LIBRARY`, if set: the full path of the library to load, and nothing
   else is tried.
2. The locations a CMake build or install recorded. A pip install records
   none.
3. The directories in `LD_LIBRARY_PATH` (Linux and the BSDs),
   `DYLD_LIBRARY_PATH` (macOS) or `PATH` (Windows, where the library is
   `stpwin.dll`).
4. The platform's own search, through `ctypes.util.find_library`: the
   `ldconfig` cache on Linux and the BSDs, the linker's default paths on
   macOS.

So an STP installed to a system prefix is found unaided. One installed
elsewhere needs its `lib` directory on the library search path, or
`STP_LIBRARY` pointing at the library.

## Example

    import stp

    s = stp.Solver()
    x = s.bitvec('x', width=8)
    s.add(x + x != 2 * x)
    print(s.check())  # False: no x makes the two differ
