# version 1.00
# usage of macro is tricky, so you may refer to the .orig file for inline form

# here we must use macro because only macro can modify the arg in outer scope 
macro(replace_msvs_mtmd_flags the_cflags bflag)
  set(loc_flag ${bflag})
  if(loc_flag)
    if(${the_cflags} MATCHES "/MD")
      #message("before replace :", "${${the_cflags}}")
      string(REGEX REPLACE "/MD" "/MT" ${the_cflags} "${${the_cflags}}")
      #message("After replace :", "${${the_cflags}}")
    endif(${the_cflags} MATCHES "/MD")
  else(loc_flag)
    # pass
    if(${the_cflags} MATCHES "/MT")
      string(REGEX REPLACE "/MT" "/MD" ${the_cflags} "${${the_cflags}}")
    endif(${the_cflags} MATCHES "/MT")
  endif(loc_flag)
endmacro(replace_msvs_mtmd_flags the_cflags bflag)

if(WIN32 AND MSVC)
  # using macro or function wpn't do the correct thing
  option(MSVC_MD "Using /MD when compiling using msvc toolchains" OFF)
  
  # get all CMAKE_CXX_FLAGS CMAKE_C_FLAGS variants
  set(BldList CMAKE_CXX_FLAGS CMAKE_C_FLAGS)
  foreach(build_typ DEBUG RELEASE MINSIZEREL RELWITHDEBINFO)
    list(APPEND BldList CMAKE_CXX_FLAGS_${build_typ} CMAKE_C_FLAGS_${build_typ})
  endforeach(build_typ DEBUG RELEASE MINSIZEREL RELWITHDEBINFO)

  # note that function or macro won't work must use global code 
  if(NOT MSVC_MD)
    foreach(flag_var ${BldList})
      replace_msvs_mtmd_flags(${flag_var} ON)
    endforeach(flag_var ${BldList})
  else(NOT MSVC_MD)
    foreach(flag_var ${BldList})
      replace_msvs_mtmd_flags(${flag_var} OFF)
    endforeach(flag_var ${BldList})
  endif(NOT MSVC_MD)
endif(WIN32 AND MSVC)
