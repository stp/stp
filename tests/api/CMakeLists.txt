option(TEST_C_API "Enable test that test STP's public C API" ON)

if(TEST_C_API)
    add_subdirectory(C)
endif()
