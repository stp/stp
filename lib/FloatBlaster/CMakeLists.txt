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

add_library(floatblaster OBJECT
    DecimalLiteral.cpp
    FloatBlaster.cpp
    FloatBlast.cpp
    FpDomainSimplify.cpp
    FpEncodingContext.cpp
    FpTotalise.cpp
    literal_fp.cpp
    symbolic_fp.cpp
)
add_dependencies(floatblaster ASTKind_header)

# DecimalLiteral.cpp is the only translation unit in STP that includes libbf.h;
# the imported target carries that include directory as SYSTEM. This replaces a
# project-wide include_directories(SYSTEM). The archive is named on libstp's
# own link line, in lib/CMakeLists.txt.
target_link_libraries(floatblaster PRIVATE LibBF)

# SymFPU is where the floating-point circuits come from: three of the sources
# here include "symfpu/core/...", and so does the internal header
# stp/FloatBlaster/symbolic_fp.h. Header-only, so the target carries an include
# directory and nothing else. This replaces a project-wide
# include_directories(SYSTEM).
target_link_libraries(floatblaster PRIVATE SymFPU)
