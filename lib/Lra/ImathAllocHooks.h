#ifndef STP_LRA_IMATH_ALLOC_HOOKS_H
#define STP_LRA_IMATH_ALLOC_HOOKS_H

#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef enum stp_lra_imath_failure
{
  STP_LRA_IMATH_FAILURE_NONE = 0,
  STP_LRA_IMATH_FAILURE_RESOURCE_LIMIT = 1,
  STP_LRA_IMATH_FAILURE_SYSTEM_ALLOCATION = 2,
  STP_LRA_IMATH_FAILURE_MISSING_SCOPE = 3,
  STP_LRA_IMATH_FAILURE_CORRUPT_METADATA = 4
} stp_lra_imath_failure;

/* The active high-level operation responsible for an IMath allocation.
 * Sites are thread-local and nest through exchange/restore, so a
 * materialisation performed inside multiplication is attributed to
 * MATERIALIZE rather than counted twice. */
typedef enum stp_lra_imath_allocation_site
{
  STP_LRA_IMATH_ALLOCATION_UNATTRIBUTED = 0,
  STP_LRA_IMATH_ALLOCATION_CONSTRUCT = 1,
  STP_LRA_IMATH_ALLOCATION_PARSE = 2,
  STP_LRA_IMATH_ALLOCATION_MATERIALIZE = 3,
  STP_LRA_IMATH_ALLOCATION_CANONICALIZE = 4,
  STP_LRA_IMATH_ALLOCATION_ADD = 5,
  STP_LRA_IMATH_ALLOCATION_SUBTRACT = 6,
  STP_LRA_IMATH_ALLOCATION_MULTIPLY = 7,
  STP_LRA_IMATH_ALLOCATION_DIVIDE = 8,
  STP_LRA_IMATH_ALLOCATION_SITE_COUNT = 9
} stp_lra_imath_allocation_site;

typedef struct stp_lra_imath_budget_state
{
  uint64_t maximum_allocation_bytes;
  uint64_t live_bytes;
  uint64_t allocation_calls;
  uint64_t allocated_bytes;
  uint64_t peak_live_bytes;
  uint64_t allocation_stops;
  uint64_t allocation_calls_by_site[STP_LRA_IMATH_ALLOCATION_SITE_COUNT];
  uint64_t allocated_bytes_by_site[STP_LRA_IMATH_ALLOCATION_SITE_COUNT];
  int stopped;
} stp_lra_imath_budget_state;

void stp_lra_imath_budget_init(stp_lra_imath_budget_state* state,
                               uint64_t maximum_allocation_bytes);
void stp_lra_imath_budget_reset_accounting(
    stp_lra_imath_budget_state* state);

stp_lra_imath_budget_state* stp_lra_imath_exchange_active_budget(
    stp_lra_imath_budget_state* state);

stp_lra_imath_allocation_site stp_lra_imath_exchange_allocation_site(
    stp_lra_imath_allocation_site site);

void stp_lra_imath_clear_failure(void);
stp_lra_imath_failure stp_lra_imath_last_failure(void);

void* stp_lra_imath_malloc(size_t size);
void* stp_lra_imath_realloc(void* pointer, size_t size);
void stp_lra_imath_free(void* pointer);

size_t stp_lra_imath_allocation_alignment(void);

#if defined(STP_LRA_TEST_FAULT_INJECTION)
void stp_lra_imath_test_fail_nth(uint64_t allocation_index);
void stp_lra_imath_test_disable_failures(void);
uint64_t stp_lra_imath_test_allocation_attempts(void);
#endif

#ifdef __cplusplus
}
#endif

/* Defined only for the two pinned IMath translation units. System allocator
 * declarations above are parsed before these target-local substitutions. */
#if defined(STP_LRA_IMATH_INTERCEPT_ALLOCATIONS)
#  define malloc(size) stp_lra_imath_malloc(size)
#  define realloc(pointer, size) stp_lra_imath_realloc((pointer), (size))
#  define free(pointer) stp_lra_imath_free(pointer)
#endif

#endif
