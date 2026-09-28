#ifndef STP_LRA_TEST_NOINLINE_H
#define STP_LRA_TEST_NOINLINE_H

// Keep replacement allocation pairs out of line. Inlining only delete's
// free() can make GCC mistake a valid new/delete pair for a new/free pair.
#if defined(_MSC_VER)
#define STP_LRA_TEST_NOINLINE __declspec(noinline)
#elif defined(__GNUC__) || defined(__clang__)
#define STP_LRA_TEST_NOINLINE __attribute__((noinline))
#else
#define STP_LRA_TEST_NOINLINE
#endif

#endif
