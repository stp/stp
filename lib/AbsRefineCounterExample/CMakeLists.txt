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

add_library(abstractionrefinement OBJECT
    AbstractionRefinement.cpp
    CounterExample.cpp
    ArrayTransformer.cpp
)
add_dependencies(abstractionrefinement ASTKind_header)

# LraCoordinator is a private libstp seam.  Its exact-core types stay
# uninstalled and are visible only to the object target that drives the
# same-candidate state machine.
target_include_directories(abstractionrefinement PRIVATE
    "${PROJECT_SOURCE_DIR}/lib/Lra")
# ExactRational.h, reached through that seam, includes <imrat.h>. Linking
# IMath here is for its INTERFACE_INCLUDE_DIRECTORIES: an OBJECT library
# links nothing, and libstp carries the archive itself. Without it this
# target compiles only while some other dependency happens to have installed
# its headers into the same directory IMath's are in.
target_link_libraries(abstractionrefinement PRIVATE IMath)
