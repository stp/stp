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

add_subdirectory(stp)
add_subdirectory(stp_simple)

option(BUILD_EXTRA_TOOLS "Build extra tools" OFF)
if (BUILD_EXTRA_TOOLS)
  add_subdirectory(rewrite_rule_gen)
  add_subdirectory(time_constantbitprop)
  add_subdirectory(measure_constantbitprop)
  add_subdirectory(test_constantbitprop)
  add_subdirectory(cvc_to_c)

  # These auxiliary tools currently produce ~78 warnings, mostly -Wswitch over
  # Kind and -Wsign-compare, so they cannot be gated on WERROR without a
  # cleanup out of proportion to simply keeping them compiling. Exempt them for
  # now, the same way lib/CMakeLists.txt exempts the vendored ABC: the -Wno-error
  # comes after the global -Werror, so it wins for these targets only and STP's
  # own libraries stay gated. Worth removing once the warnings are fixed.
  if (WERROR AND NOT MSVC)
    foreach(_extra_tool rewrite_rule_gen time_constantbitprop measure
                        test_constantbitprop cvc_to_c)
      if (TARGET ${_extra_tool})
        target_compile_options(${_extra_tool} PRIVATE -Wno-error)
      endif()
    endforeach()
  endif()
endif()
