# version 1.00
# gcc -static-libgcc should be specified

# here we must use macro because only macro can modify the arg in outer scope 
macro(replace_gcc_flags the_cflags bflag)
  set(loc_flag ${bflag})
  if(loc_flag)
    if(${the_cflags} MATCHES "-shared-libgcc")
      string(REGEX REPLACE "-shared-libgcc" "-static-libgcc" ${the_cflags} "${${the_cflags}}")
    else(${the_cflags} MATCHES "-shared-libgcc")
      set(${the_cflags} "${${the_cflags}} -static-libgcc")
    endif(${the_cflags} MATCHES "-shared-libgcc")
  else(loc_flag)
    # pass
    if(${the_cflags} MATCHES "-static-libgcc")
      string(REGEX REPLACE "-static-libgcc" "-shared-libgcc" ${the_cflags} "${${the_cflags}}")
    else(${the_cflags} MATCHES "-static-libgcc")
      set(${the_cflags} "${${the_cflags}} -shared-libgcc")
    endif(${the_cflags} MATCHES "-static-libgcc")
  endif(loc_flag)
endmacro(replace_gcc_flags the_cflags bflag)

if(UNIX)
  # using macro or function wpn't do the correct thing
  option(USING_GCC_SHARED_RUNTIME_LIB "Using -shared-libgcc not -static-libgcc when compiling using gcc toolchains" OFF)
  
  # get all CMAKE_CXX_FLAGS CMAKE_C_FLAGS variants
  set(BldList CMAKE_CXX_FLAGS CMAKE_C_FLAGS)
  foreach(build_typ DEBUG RELEASE MINSIZEREL RELWITHDEBINFO)
    list(APPEND BldList CMAKE_CXX_FLAGS_${build_typ} CMAKE_C_FLAGS_${build_typ})
  endforeach(build_typ DEBUG RELEASE MINSIZEREL RELWITHDEBINFO)

  # note that if function or macro not work we must use global code 
  if(NOT USING_GCC_SHARED_RUNTIME_LIB)
    foreach(flag_var ${BldList})
      replace_gcc_flags(${flag_var} ON)
    endforeach(flag_var ${BldList})
  else(NOT USING_GCC_SHARED_RUNTIME_LIB)
    foreach(flag_var ${BldList})
      replace_gcc_flags(${flag_var} OFF)
    endforeach(flag_var ${BldList})
  endif(NOT USING_GCC_SHARED_RUNTIME_LIB)
endif(UNIX)


