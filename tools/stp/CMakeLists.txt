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
if (Boost_FOUND)
    include_directories(${Boost_INCLUDE_DIR})
    add_executable(stp
        main.cpp
        main_common.cpp
        STPProgramGlobals.cpp
    )

    if (STATICCOMPILE)
        set_target_properties(stp PROPERTIES LINK_SEARCH_START_STATIC 1)
    endif()

    set_target_properties(stp PROPERTIES
      RUNTIME_OUTPUT_DIRECTORY "${PROJECT_BINARY_DIR}"
      VERSION "${PROJECT_VERSION}"
    )
    if (STATICCOMPILE)
        set_target_properties(stp PROPERTIES LINK_SEARCH_END_STATIC 1)
    endif()

    target_link_libraries(stp libstp)
    install(TARGETS stp
        EXPORT ${STP_EXPORT_NAME}
        RUNTIME DESTINATION bin
    )
endif()
