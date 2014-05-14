option(TEST_C_API "Enable tests that test STP's public C API" ON)

if(TEST_C_API)
    add_subdirectory(C)
endif()

if(ENABLE_PYTHON_INTERFACE)
    option(TEST_PYTHON_API "Enable tests that test STP's public Python API" ON)
endif()

if(TEST_PYTHON_API)
    add_subdirectory(python)
endif()
