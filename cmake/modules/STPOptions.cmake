# AUTHORS: Andrew Teylu
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

# Three-valued options.
#
# A plain option() cannot tell "the user asked for OFF" from "nobody said
# anything and the default is OFF": both leave the same value in the cache.
# That matters wherever the build wants to pick a default from something else
# it has worked out -- the build type, or whether a library was found -- while
# still letting an explicit -D win. Done with option(), the derived value
# silently overwrites the user's, which is what ENABLE_ASSERTIONS did under
# CMAKE_BUILD_TYPE=Release for years.
#
# So: declare with stp_option(), which leaves the cache holding the string
# IGNORE until someone passes -DVAR=ON or -DVAR=OFF; then use stp_set_option()
# to supply the derived default, which applies only to a variable still sitting
# at IGNORE.
#
# IGNORE is CMake's own spelling for this. if() treats it as false, so a
# variable left at IGNORE reads as OFF everywhere downstream -- which is the
# right reading for a feature nobody enabled, and means only the code that
# actually cares about the distinction has to mention it.

macro(stp_option var description)
    set(${var} IGNORE CACHE STRING "${description}")
    # Give cmake-gui and ccmake a drop-down rather than a free-text box.
    set_property(CACHE ${var} PROPERTY STRINGS IGNORE ON OFF)
endmacro()

# Set var to value, but only if the user has not chosen for themselves.
macro(stp_set_option var value)
    if(${var} STREQUAL "IGNORE")
        set(${var} ${value})
    endif()
endmacro()

# True when the user passed -D${var}= explicitly, false when it is still at the
# tri-state default. Only for the cases where "unset" needs to mean something
# other than "off" -- an auto-detected dependency, say, where an explicit ON
# must be a hard error if it is missing but a defaulted ON may quietly give up.
macro(stp_option_is_explicit var out)
    if(${var} STREQUAL "IGNORE")
        set(${out} FALSE)
    else()
        set(${out} TRUE)
    endif()
endmacro()

# A build directory configured before a variable was converted from option() to
# stp_option() holds it as a BOOL, where ON is indistinguishable from an
# explicit request -- so reconfiguring would silently promote a default into a
# choice. Retype such an entry back to the tri-state's "unset" value once.
#
# The cost is that a deliberate -D${var}= in an existing build directory has to
# be passed again on the first reconfigure after the conversion. That is the
# lesser of the two surprises: the alternative is a Release build that starts
# asserting because its cache said ON when nobody had asked.
macro(stp_migrate_bool_option var)
    get_property(_stp_mbo_type CACHE ${var} PROPERTY TYPE)
    if(_stp_mbo_type STREQUAL "BOOL")
        message(STATUS
            "${var} is now a three-valued option (IGNORE/ON/OFF); discarding "
            "the cached BOOL from an earlier configure. Pass -D${var}= again "
            "if you had chosen something other than the default.")
        unset(${var} CACHE)
    endif()
    unset(_stp_mbo_type)
endmacro()

# EOF
