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

# -----------------------------------------------------------------------------
# Create binary
# -----------------------------------------------------------------------------
add_executable(stp_simple
    main_simple.cpp
    ../stp/main_common.cpp
)

if (STATICCOMPILE)
    set_target_properties(stp_simple PROPERTIES LINK_SEARCH_START_STATIC 1)
endif()
set_target_properties(stp_simple PROPERTIES
    RUNTIME_OUTPUT_DIRECTORY ${PROJECT_BINARY_DIR})
if (STATICCOMPILE)
    set_target_properties(stp_simple PROPERTIES LINK_SEARCH_END_STATIC 1)
endif()
target_link_libraries(stp_simple libstp)

install(TARGETS stp_simple
        EXPORT ${STP_EXPORT_NAME}
        RUNTIME DESTINATION ${BINDIR}
)
