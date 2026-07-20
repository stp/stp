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

if (NOT ONLY_SIMPLE)
    set(STP_EXECUTABLE_PATH "$<TARGET_FILE:stp-bin>")
else()
    set(STP_EXECUTABLE_PATH "$<TARGET_FILE:stp_simple-bin>")
endif()

# Create llvm-lit configuration file
configure_file(lit.site.cfg.in lit.site.cfg.g @ONLY)
file(GENERATE OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/$<CONFIG>.site.cfg
              INPUT ${CMAKE_CURRENT_BINARY_DIR}/lit.site.cfg.g)

add_test(NAME query-files
    COMMAND ${LIT_TOOL} ${LIT_ARGS} --config-prefix=$<CONFIG> .
    WORKING_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}"
)
