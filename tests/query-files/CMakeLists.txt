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

if (Boost_FOUND)
    get_target_property(STP_EXECUTABLE_PATH stp LOCATION)
else()
    get_target_property(STP_EXECUTABLE_PATH stp_simple LOCATION)
endif()

# Create llvm-lit configuration file
configure_file(lit.site.cfg.in lit.site.cfg @ONLY)

if (Boost_FOUND)
    add_custom_target(query-file-tests
                  DEPENDS stp
                  COMMAND ${LIT_TOOL} ${LIT_ARGS} .
    )
else()
    add_custom_target(query-file-tests
                  DEPENDS stp_simple
                  COMMAND ${LIT_TOOL} ${LIT_ARGS} .
    )
endif()

# Make sure this test-suite runs when "check" is target
add_dependencies(check query-file-tests)