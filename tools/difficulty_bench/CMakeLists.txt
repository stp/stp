# AUTHORS: Trevor Hansen
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

add_executable(difficulty_bench
    main.cpp
)

# difficulty_bench builds the AIG itself rather than reaching it through
# libstp: BBNodeManagerAIG's inline constructor and destructor call
# Aig_ManStart and Aig_ManStop. libstp localises the ABC symbols it links
# (--exclude-libs, see lib/CMakeLists.txt), so a direct user of ABC has to
# link it directly.
target_link_libraries(difficulty_bench
    stp
    ABC
)
# $<TARGET_FILE:...> names a file rather than a target, so the build order has
# to be spelled out, exactly as lib/CMakeLists.txt does for libstp.
