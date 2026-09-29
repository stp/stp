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


# FIXME: Merge into one library
#
# The engine's C++ interface, which the parsers and the 3.x API use. The 2.x C
# API is not part of libstp: libstp2 (lib/Compat2) provides it.
add_library(cppinterface OBJECT
    cpp_interface.cpp
    SMT2Output.cpp
)

add_dependencies(cppinterface ASTKind_header)

# Reaches the exact-rational header, which includes <imrat.h>. For IMath's
# INTERFACE_INCLUDE_DIRECTORIES; see the note in
# lib/AbsRefineCounterExample/CMakeLists.txt.
target_link_libraries(cppinterface PRIVATE IMath)
