# AUTHORS: Dan Liew, Ryan Govostes, Mate Soos
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# # furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
# THE SOFTWARE.

# -----------------------------------------------------------------------------
# Setup python module in build directory
# -----------------------------------------------------------------------------

# The binary path isn't known until the build process starts
# (e.g. when building with MSBuild), so generate the file lately.)

# get_property(STP_LIB_LOCATION TARGET stp PROPERTY LOCATION)
# file(MAKE_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/$<CONFIG>)

# The ctypes package loads one shared library by name and expects the 2.x C
# API in it: libstp while that API is compiled into libstp, libstp2 when
# STP_LEGACY_C_INTERFACE is off (libstp2 pulls libstp in as a dependency).
if(STP_LEGACY_C_INTERFACE)
    get_target_property(LIBSTP_BASENAME stp OUTPUT_NAME)
else()
    get_target_property(LIBSTP_BASENAME stp2 OUTPUT_NAME)
endif()
set(LIBSTP_FILENAME "${CMAKE_SHARED_LIBRARY_PREFIX}${LIBSTP_BASENAME}${CMAKE_SHARED_LIBRARY_SUFFIX}")

#
# 'library_path.py.in' has some code that is conditional on being on Win32 or
# not -- rather than have two `.in` files, we leave the non-Win32 code comment
# out.
#
if(WIN32)
  set(WIN32PYTHONCOMMENT "")
else()
  set(WIN32PYTHONCOMMENT "#")
endif()

configure_file(${CMAKE_CURRENT_SOURCE_DIR}/library_path.py.in
               ${CMAKE_CURRENT_BINARY_DIR}/library_path.py @ONLY)

# The rest of the package is plain Python, shared with the pip install
# (bindings/python/pyproject.toml); only library_path.py is generated.
configure_file(${CMAKE_CURRENT_SOURCE_DIR}/stp.py
               ${CMAKE_CURRENT_BINARY_DIR}/stp.py COPYONLY)

configure_file(${CMAKE_CURRENT_SOURCE_DIR}/__init__.py
               ${CMAKE_CURRENT_BINARY_DIR}/__init__.py COPYONLY)

# -----------------------------------------------------------------------------
# Not installed: the installed `stp` Python package is the 3.x one
# (bindings/python3). This 2.x package stays in the build tree, where its tests
# (tests/api/python) run it.
# -----------------------------------------------------------------------------
