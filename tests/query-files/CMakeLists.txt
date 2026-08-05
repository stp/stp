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

# A Python literal for lit.site.cfg.in: CMake booleans render as ON/OFF.
if (ENABLE_FLOATING_POINT)
    set(STP_FLOATING_POINT_PYBOOL "True")
else()
    set(STP_FLOATING_POINT_PYBOOL "False")
endif()

# Create llvm-lit configuration file
configure_file(lit.site.cfg.in lit.site.cfg.g @ONLY)
file(GENERATE OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/$<CONFIG>.site.cfg
              INPUT ${CMAKE_CURRENT_BINARY_DIR}/lit.site.cfg.g)

add_test(NAME query-files
    COMMAND ${LIT_TOOL} ${LIT_ARGS} --config-prefix=$<CONFIG> .
    WORKING_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}"
)

# The run above only exercises CaDiCaL's bounded variable addition where the
# AUTO default turns it on (array problems). Forcing it on for the whole
# corpus also covers the declare/translate machinery on problems the
# heuristic would leave alone, so a numbering mistake cannot hide behind the
# heuristic. Only registered when the flag can actually engage; on pre-3.0
# CaDiCaL builds the sweep would just repeat the run above behind warnings.
if (USE_CADICAL AND CADICAL_HAS_FACTOR)
    add_test(NAME query-files-cadical-factor
        COMMAND ${LIT_TOOL} ${LIT_ARGS} --config-prefix=$<CONFIG>
                --param solver_params=--cadical-factor=on .
        WORKING_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}"
    )
    # Both lit invocations write per-test Output/ files into this same
    # directory, so running them concurrently under ctest -j corrupts each
    # other's results. Serialise them against each other (only).
    set_tests_properties(query-files query-files-cadical-factor
        PROPERTIES RESOURCE_LOCK query-files-exec-root
    )
endif()
