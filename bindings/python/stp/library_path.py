# Locations to try for libstp before the platform's own library search.
#
# This is the copy a pip install ships, and it names none: an STP installed
# with CMake is found through the library search path (ldconfig,
# LD_LIBRARY_PATH, DYLD_LIBRARY_PATH or PATH), or through STP_LIBRARY. A CMake
# build or install of the bindings replaces this file with one generated from
# library_path.py.in or library_path.py.in_install, which lists where that
# build put the library.
PATHS = []
