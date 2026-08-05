# AUTHORS: Andrew Teylu
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

# FloatBlaster.cpp and FpTotalise.cpp always build: withFormat/FpTotalise
# are SymFPU-free, and without ENABLE_FLOATING_POINT the blast entry points
# become "built without floating-point support" stubs (the ifdefs are in
# FloatBlaster.cpp). Only symbolic_fp.cpp -- the SymFPU backend -- needs
# the library itself. DecimalLiteral.cpp follows the stub pattern: it always
# builds so the parser always links, and without STP_HAVE_LIBBF (set by the
# USE_LIBBF block in the top-level CMakeLists.txt) its one function is a
# "cannot convert real literals" refusal.
set(floatblaster_sources
    DecimalLiteral.cpp
    FloatBlaster.cpp
    FloatBlast.cpp
    FpEncodingContext.cpp
    FpTotalise.cpp
)
if (ENABLE_FLOATING_POINT)
    list(APPEND floatblaster_sources symbolic_fp.cpp)
endif()
add_library(floatblaster OBJECT ${floatblaster_sources})
add_dependencies(floatblaster ASTKind_header)
