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

set(STP_EXECUTABLE_PATH "$<TARGET_FILE:stp-bin>")

# A Python literal for lit.site.cfg.in: CMake booleans render as ON/OFF.
if (USE_MINISAT)
    set(STP_MINISAT_PYBOOL "True")
else()
    set(STP_MINISAT_PYBOOL "False")
endif()
if (USE_CADICAL)
    set(STP_CADICAL_PYBOOL "True")
else()
    set(STP_CADICAL_PYBOOL "False")
endif()
if (CADICAL_HAS_INPROBING)
    set(STP_CADICAL_INPROBING_PYBOOL "True")
else()
    set(STP_CADICAL_INPROBING_PYBOOL "False")
endif()

# Create llvm-lit configuration file
configure_file(lit.site.cfg.in lit.site.cfg.g @ONLY)
file(GENERATE OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/$<CONFIG>.site.cfg
              INPUT ${CMAKE_CURRENT_BINARY_DIR}/lit.site.cfg.g)

add_test(NAME query-files
    COMMAND ${LIT_TOOL} ${LIT_ARGS} --config-prefix=$<CONFIG> .
    WORKING_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}"
)

# CaDiCaL's bounded variable addition is on by default, so the run above
# already covers the declare/translate machinery across the whole corpus --
# every STP variable travels through the translation table there. What it no
# longer covers is the other side of the switch, so the sweep forces the
# factor off instead: the untranslated path has to keep answering identically.
# Only registered when the flag can engage at all; on pre-3.0 CaDiCaL builds
# the factor is never on in the first place and the sweep would just repeat
# the run above.
if (USE_CADICAL AND CADICAL_HAS_FACTOR)
    add_test(NAME query-files-cadical-factor-off
        COMMAND ${LIT_TOOL} ${LIT_ARGS} --config-prefix=$<CONFIG>
                --param solver_params=--cadical-factor=off .
        WORKING_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}"
    )
    # Both lit invocations write per-test Output/ files into this same
    # directory, so running them concurrently under ctest -j corrupts each
    # other's results. Serialise them against each other (only).
    set_tests_properties(query-files query-files-cadical-factor-off
        PROPERTIES RESOURCE_LOCK query-files-exec-root
    )
endif()
