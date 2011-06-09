# version 1.00
# to make msvc/gcc to link statically the runtime libraries  
get_filename_component(MYMODESDIR ${CMAKE_CURRENT_LIST_FILE} PATH)
include("${MYMODESDIR}/msvcmt.cmake")
include("${MYMODESDIR}/slibgcc.cmake")

