# Copyright (c)
#     2015 Dan Liew
#     2015 Ryan Gvostes
#     2015 Mate Soos
#     2015 Marko Dimjašević
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

option(BUILD_EXTRA_TOOLS "Build extra tools" ON)
if (BUILD_EXTRA_TOOLS)
  add_subdirectory(stp_constantbitprop)
  add_subdirectory(rewrite_rule_gen)
  # FIXME: Decide what to do with these
  add_subdirectory(time_constantbitprop)
  # These are broken
  # add_subdirectory(measure)
  # add_subdirectory(test_constantbitprop)
endif()
