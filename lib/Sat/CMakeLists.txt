# AUTHORS: Dan Liew, Ryan Gvostes, Mate Soos
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

set(sat_lib_to_add
    MinisatCore.cpp
    SimplifyingMinisat.cpp
)

if(HAVE_FLAG_CPP03 AND HAVE_FLAG_STD_CPP11)
  set_source_files_properties(MinisatCore.cpp PROPERTIES COMPILE_FLAGS -std=c++03)
  set_source_files_properties(SimplifyingMinisat.cpp PROPERTIES COMPILE_FLAGS -std=c++03)
endif()

if (USE_CRYPTOMINISAT4)
    set(sat_lib_to_add ${sat_lib_to_add} CryptoMinisat4.cpp)
endif()

add_library(sat OBJECT ${sat_lib_to_add})

