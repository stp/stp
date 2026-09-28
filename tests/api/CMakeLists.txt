# AUTHORS: Dan Liew, Ryan Govostes, Mate Soos
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
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

option(TEST_C_API "Enable tests that test STP's public C APIs" ON)

if(TEST_C_API)
    # the 3.x C API
    add_subdirectory(c)
    # libstp2: the 2.x C API over the 3.x one
    add_subdirectory(compat2)
endif()
option(TEST_CPP_API "Enable tests that test STP's 3.x C++ API" ON)
if(TEST_CPP_API)
    add_subdirectory(cpp)
endif()

# the 3.x Python API (pytest over the package built in bindings/python3)
if(ENABLE_PYTHON3_API)
    add_subdirectory(python)
endif()

# Exercise the installed package as an external UF C++ consumer. DESTDIR is
# used by the driver, so even configurations whose install prefix is /usr/local
# remain confined to the build tree.
if(UNIX)
    add_subdirectory(install)
endif()
