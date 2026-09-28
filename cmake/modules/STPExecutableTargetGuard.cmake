# Resolve an option-controlled executable target exactly once, after the target
# producer has been visited.  A supported option-OFF profile yields FALSE;
# either inconsistent state is a configure error rather than a silent test
# omission.
function(stp_resolve_option_target_availability)
  set(options)
  set(one_value_args TARGET OPTION OUT_VAR)
  cmake_parse_arguments(PARSE_ARGV 0 STP_TARGET_GUARD
    "${options}" "${one_value_args}" "")

  if(STP_TARGET_GUARD_UNPARSED_ARGUMENTS OR
     NOT STP_TARGET_GUARD_TARGET OR
     NOT STP_TARGET_GUARD_OPTION OR
     NOT STP_TARGET_GUARD_OUT_VAR)
    message(FATAL_ERROR
      "stp_resolve_option_target_availability requires TARGET, OPTION, and OUT_VAR")
  endif()
  if(NOT DEFINED ${STP_TARGET_GUARD_OPTION})
    message(FATAL_ERROR
      "STP target availability guard: option ${STP_TARGET_GUARD_OPTION} is undefined")
  endif()

  set(stp_target_guard_option_value "${${STP_TARGET_GUARD_OPTION}}")
  if(stp_target_guard_option_value)
    if(NOT TARGET ${STP_TARGET_GUARD_TARGET})
      message(FATAL_ERROR
        "STP target availability mismatch: ${STP_TARGET_GUARD_OPTION} is enabled "
        "but target ${STP_TARGET_GUARD_TARGET} is absent")
    endif()
    set(stp_target_guard_available TRUE)
  else()
    if(TARGET ${STP_TARGET_GUARD_TARGET})
      message(FATAL_ERROR
        "STP target availability mismatch: ${STP_TARGET_GUARD_OPTION} is disabled "
        "but target ${STP_TARGET_GUARD_TARGET} exists")
    endif()
    set(stp_target_guard_available FALSE)
  endif()

  set(${STP_TARGET_GUARD_OUT_VAR} "${stp_target_guard_available}" PARENT_SCOPE)
endfunction()
