# A deliberately small, standalone benchmark for the C Expr ownership path.
# It is built with the tests (and with the other developer tools) but is not a
# CTest: timing and peak-RSS thresholds are machine- and allocator-dependent.
add_executable(c_handle_churn_benchmark c_handle_churn_benchmark.cpp)
# STP_LEGACY_C_LINK is libstp2 when the 2.x C API this benchmark drives is
# not part of libstp (STP_LEGACY_C_INTERFACE=OFF), and empty otherwise.
target_link_libraries(c_handle_churn_benchmark ${STP_ALLOCATOR_LIBRARY} ${STP_LEGACY_C_LINK} stp)
