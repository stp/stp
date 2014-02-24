find_package(PythonInterp REQUIRED)

if(NOT PYTHONINTERP_FOUND)
    message(FATAL_ERROR "Python cannot be found")
endif()
