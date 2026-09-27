# STP's 2.x Python bindings

The 2.x Python bindings of [STP](https://github.com/stp/stp). They are pure
Python and load `libstp2`, the library that provides STP's 2.x C API, through
`ctypes`, so one copy of the package works under every Python 3 and nothing
needs compiling. STP's CMake build builds them for their tests and does not
install them: the installed `stp` package is the 3.x one, in
`bindings/python3`.

## Installing them

With pip, against an STP that is already installed (a shared-library build,
the default), once per Python interpreter:

    python3 -m pip install ./bindings/python

## Finding libstp2

At import, the package tries, in order:

1. `STP_LIBRARY`, if set: the full path of the library to load, and nothing
   else is tried.
2. The locations a CMake build recorded. A pip install records none.
3. The directories in `LD_LIBRARY_PATH` (Linux and the BSDs),
   `DYLD_LIBRARY_PATH` (macOS) or `PATH` (Windows, where the library is
   `stp2win.dll`).
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
