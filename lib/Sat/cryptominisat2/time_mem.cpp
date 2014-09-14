#if defined(__APPLE__)
/* the #include below #define TRUE, which conflicts with STP's TRUE in ASTKind.h */
#include <malloc/malloc.h>

double memUsed(void) {
    malloc_statistics_t t;
    malloc_zone_statistics(NULL, &t);
    return (double)t.max_size_in_use / (1024*1024);
}
#endif
