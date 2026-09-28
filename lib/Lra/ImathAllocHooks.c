#include "ImathAllocHooks.h"

#include <limits.h>
#include <stdint.h>

#if defined(_MSC_VER)
#  define STP_LRA_THREAD_LOCAL __declspec(thread)
#elif defined(__GNUC__) || defined(__clang__)
#  define STP_LRA_THREAD_LOCAL __thread
#else
#  error "A compiler-supported thread-local storage specifier is required"
#endif

#define STP_LRA_ALLOCATION_MAGIC UINT64_C(0x5354504c5241494d)

#if defined(_MSC_VER)
#  define STP_LRA_ALIGNMENT_PREFIX __declspec(align(16))
#  define STP_LRA_ALIGNMENT_SUFFIX
#elif defined(__BIGGEST_ALIGNMENT__)
#  define STP_LRA_ALIGNMENT_PREFIX
#  define STP_LRA_ALIGNMENT_SUFFIX \
    __attribute__((aligned(__BIGGEST_ALIGNMENT__)))
#else
#  error "A compiler maximum-alignment declaration is required"
#endif

typedef union stp_lra_imath_allocation_header stp_lra_imath_allocation_header;

STP_LRA_ALIGNMENT_PREFIX union stp_lra_imath_allocation_header
{
  struct
  {
    uint64_t magic;
    size_t payload_size;
    stp_lra_imath_budget_state* owner;
    stp_lra_imath_allocation_header* previous;
    stp_lra_imath_allocation_header* next;
  } metadata;
  void* pointer_alignment;
  uint64_t integer_alignment;
} STP_LRA_ALIGNMENT_SUFFIX;

typedef struct stp_lra_imath_alignment_probe
{
  char byte;
  stp_lra_imath_allocation_header value;
} stp_lra_imath_alignment_probe;

static STP_LRA_THREAD_LOCAL stp_lra_imath_budget_state* active_budget;
static STP_LRA_THREAD_LOCAL stp_lra_imath_failure last_failure;
static STP_LRA_THREAD_LOCAL stp_lra_imath_allocation_header* live_blocks;
static STP_LRA_THREAD_LOCAL stp_lra_imath_allocation_site active_site;

#if defined(STP_LRA_TEST_FAULT_INJECTION)
static STP_LRA_THREAD_LOCAL uint64_t fault_index = UINT64_MAX;
static STP_LRA_THREAD_LOCAL uint64_t fault_attempts;
#endif

static uint64_t saturating_add(uint64_t left, uint64_t right)
{
  return UINT64_MAX - left < right ? UINT64_MAX : left + right;
}

static void mark_failure(stp_lra_imath_failure failure)
{
  last_failure = failure;
}

static void mark_resource_stop(stp_lra_imath_budget_state* state)
{
  state->allocation_stops = saturating_add(state->allocation_stops, 1);
  state->stopped = 1;
  mark_failure(STP_LRA_IMATH_FAILURE_RESOURCE_LIMIT);
}

static int total_size(size_t payload_size, size_t* total)
{
  size_t const effective_payload = payload_size == 0 ? 1 : payload_size;
  if (SIZE_MAX - sizeof(stp_lra_imath_allocation_header) <
      effective_payload)
  {
    return 0;
  }
  *total = sizeof(stp_lra_imath_allocation_header) + effective_payload;
  return 1;
}

/* Whether a payload is too large for the uint64_t accounting to record.
 * Only a size_t wider than 64 bits can be; with any other the comparison is
 * constant, and -Wtype-limits rejects it on a 32-bit target. */
static int exceeds_accounting(size_t payload_size)
{
#if SIZE_MAX > UINT64_MAX
  return payload_size > UINT64_MAX;
#else
  (void)payload_size;
  return 0;
#endif
}

static void link_block(stp_lra_imath_allocation_header* header)
{
  header->metadata.previous = NULL;
  header->metadata.next = live_blocks;
  if (live_blocks != NULL)
  {
    live_blocks->metadata.previous = header;
  }
  live_blocks = header;
}

static void unlink_block(stp_lra_imath_allocation_header* header)
{
  if (header->metadata.previous != NULL)
  {
    header->metadata.previous->metadata.next = header->metadata.next;
  }
  else
  {
    live_blocks = header->metadata.next;
  }
  if (header->metadata.next != NULL)
  {
    header->metadata.next->metadata.previous = header->metadata.previous;
  }
  header->metadata.previous = NULL;
  header->metadata.next = NULL;
}

/* The header sits directly before the payload, so it is found by
 * arithmetic; what the walk over every live block used to establish -- that
 * the pointer is one of ours -- the magic and the block's own links
 * establish in constant time. The walk made every free cost the number of
 * live values, which on a dense problem with wide coefficients was most of
 * the run. */
static stp_lra_imath_allocation_header* find_block(void* pointer)
{
  stp_lra_imath_allocation_header* header =
      (stp_lra_imath_allocation_header*)pointer - 1;
  if (header->metadata.magic != STP_LRA_ALLOCATION_MAGIC)
  {
    return NULL;
  }
  if (header->metadata.previous == NULL
          ? live_blocks != header
          : header->metadata.previous->metadata.next != header)
  {
    return NULL;
  }
  if (header->metadata.next != NULL &&
      header->metadata.next->metadata.previous != header)
  {
    return NULL;
  }
  return header;
}

static int fault_requested(void)
{
#if defined(STP_LRA_TEST_FAULT_INJECTION)
  uint64_t const current = fault_attempts;
  fault_attempts = saturating_add(fault_attempts, 1);
  return current == fault_index;
#else
  return 0;
#endif
}

static void record_attempt(stp_lra_imath_budget_state* state)
{
  state->allocation_calls = saturating_add(state->allocation_calls, 1);
  state->allocation_calls_by_site[active_site] =
      saturating_add(state->allocation_calls_by_site[active_site], 1);
}

static int can_set_live_bytes(stp_lra_imath_budget_state* state,
                              uint64_t old_size,
                              uint64_t new_size,
                              uint64_t* new_live)
{
  if (state->live_bytes < old_size)
  {
    mark_failure(STP_LRA_IMATH_FAILURE_CORRUPT_METADATA);
    state->stopped = 1;
    return 0;
  }
  *new_live = state->live_bytes - old_size;
  if (UINT64_MAX - *new_live < new_size)
  {
    mark_resource_stop(state);
    return 0;
  }
  *new_live += new_size;
  if (*new_live > state->maximum_allocation_bytes)
  {
    mark_resource_stop(state);
    return 0;
  }
  return 1;
}

static void record_success(stp_lra_imath_budget_state* state,
                           uint64_t requested_size,
                           uint64_t new_live)
{
  state->live_bytes = new_live;
  state->allocated_bytes =
      saturating_add(state->allocated_bytes, requested_size);
  state->allocated_bytes_by_site[active_site] = saturating_add(
      state->allocated_bytes_by_site[active_site], requested_size);
  if (state->peak_live_bytes < new_live)
  {
    state->peak_live_bytes = new_live;
  }
}

void stp_lra_imath_budget_init(stp_lra_imath_budget_state* state,
                               uint64_t maximum_allocation_bytes)
{
  size_t site;
  state->maximum_allocation_bytes = maximum_allocation_bytes;
  state->live_bytes = 0;
  state->allocation_calls = 0;
  state->allocated_bytes = 0;
  state->peak_live_bytes = 0;
  state->allocation_stops = 0;
  for (site = 0; site < STP_LRA_IMATH_ALLOCATION_SITE_COUNT; ++site)
  {
    state->allocation_calls_by_site[site] = 0;
    state->allocated_bytes_by_site[site] = 0;
  }
  state->stopped = 0;
}

void stp_lra_imath_budget_reset_accounting(
    stp_lra_imath_budget_state* state)
{
  size_t site;
  state->allocation_calls = 0;
  state->allocated_bytes = 0;
  state->peak_live_bytes = state->live_bytes;
  state->allocation_stops = 0;
  for (site = 0; site < STP_LRA_IMATH_ALLOCATION_SITE_COUNT; ++site)
  {
    state->allocation_calls_by_site[site] = 0;
    state->allocated_bytes_by_site[site] = 0;
  }
  state->stopped = 0;
}

stp_lra_imath_budget_state* stp_lra_imath_exchange_active_budget(
    stp_lra_imath_budget_state* state)
{
  stp_lra_imath_budget_state* previous = active_budget;
  active_budget = state;
  return previous;
}

stp_lra_imath_allocation_site stp_lra_imath_exchange_allocation_site(
    stp_lra_imath_allocation_site site)
{
  stp_lra_imath_allocation_site previous = active_site;
  if (site < 0 || site >= STP_LRA_IMATH_ALLOCATION_SITE_COUNT)
  {
    active_site = STP_LRA_IMATH_ALLOCATION_UNATTRIBUTED;
    mark_failure(STP_LRA_IMATH_FAILURE_CORRUPT_METADATA);
  }
  else
  {
    active_site = site;
  }
  return previous;
}

void stp_lra_imath_clear_failure(void)
{
  last_failure = STP_LRA_IMATH_FAILURE_NONE;
}

stp_lra_imath_failure stp_lra_imath_last_failure(void)
{
  return last_failure;
}

void* stp_lra_imath_malloc(size_t size)
{
  stp_lra_imath_budget_state* owner = active_budget;
  stp_lra_imath_allocation_header* header;
  uint64_t new_live;
  size_t bytes;

  if (owner == NULL)
  {
    mark_failure(STP_LRA_IMATH_FAILURE_MISSING_SCOPE);
    return NULL;
  }
  record_attempt(owner);
  if (fault_requested())
  {
    mark_failure(STP_LRA_IMATH_FAILURE_SYSTEM_ALLOCATION);
    return NULL;
  }
  if (exceeds_accounting(size) || !total_size(size, &bytes))
  {
    mark_resource_stop(owner);
    return NULL;
  }
  if (!can_set_live_bytes(owner, 0, (uint64_t)size, &new_live))
  {
    return NULL;
  }
  header = (stp_lra_imath_allocation_header*)malloc(bytes);
  if (header == NULL)
  {
    mark_failure(STP_LRA_IMATH_FAILURE_SYSTEM_ALLOCATION);
    return NULL;
  }
  header->metadata.magic = STP_LRA_ALLOCATION_MAGIC;
  header->metadata.payload_size = size;
  header->metadata.owner = owner;
  link_block(header);
  record_success(owner, (uint64_t)size, new_live);
  return (void*)(header + 1);
}

void* stp_lra_imath_realloc(void* pointer, size_t size)
{
  stp_lra_imath_allocation_header* header;
  stp_lra_imath_allocation_header* replacement;
  stp_lra_imath_budget_state* owner;
  uint64_t new_live;
  size_t bytes;
  size_t old_size;

  if (pointer == NULL)
  {
    return stp_lra_imath_malloc(size);
  }
  header = find_block(pointer);
  if (header == NULL || header->metadata.magic != STP_LRA_ALLOCATION_MAGIC)
  {
    mark_failure(STP_LRA_IMATH_FAILURE_CORRUPT_METADATA);
    return NULL;
  }
  owner = header->metadata.owner;
  if (active_budget == NULL)
  {
    mark_failure(STP_LRA_IMATH_FAILURE_MISSING_SCOPE);
    return NULL;
  }
  if (active_budget != owner)
  {
    mark_failure(STP_LRA_IMATH_FAILURE_CORRUPT_METADATA);
    active_budget->stopped = 1;
    return NULL;
  }
  record_attempt(owner);
  if (size == 0)
  {
    stp_lra_imath_free(pointer);
    return NULL;
  }
  if (fault_requested())
  {
    mark_failure(STP_LRA_IMATH_FAILURE_SYSTEM_ALLOCATION);
    return NULL;
  }
  old_size = header->metadata.payload_size;
  if (exceeds_accounting(size) || !total_size(size, &bytes))
  {
    mark_resource_stop(owner);
    return NULL;
  }
  if (!can_set_live_bytes(owner, (uint64_t)old_size, (uint64_t)size,
                          &new_live))
  {
    return NULL;
  }

  unlink_block(header);
  replacement = (stp_lra_imath_allocation_header*)realloc(header, bytes);
  if (replacement == NULL)
  {
    link_block(header);
    mark_failure(STP_LRA_IMATH_FAILURE_SYSTEM_ALLOCATION);
    return NULL;
  }
  replacement->metadata.magic = STP_LRA_ALLOCATION_MAGIC;
  replacement->metadata.payload_size = size;
  replacement->metadata.owner = owner;
  link_block(replacement);
  record_success(owner, (uint64_t)size, new_live);
  return (void*)(replacement + 1);
}

void stp_lra_imath_free(void* pointer)
{
  stp_lra_imath_allocation_header* header;
  stp_lra_imath_budget_state* owner;
  size_t size;

  if (pointer == NULL)
  {
    return;
  }
  header = find_block(pointer);
  if (header == NULL || header->metadata.magic != STP_LRA_ALLOCATION_MAGIC)
  {
    mark_failure(STP_LRA_IMATH_FAILURE_CORRUPT_METADATA);
    return;
  }
  owner = header->metadata.owner;
  size = header->metadata.payload_size;
  unlink_block(header);
  header->metadata.magic = 0;
  if (owner == NULL || owner->live_bytes < size)
  {
    mark_failure(STP_LRA_IMATH_FAILURE_CORRUPT_METADATA);
    if (owner != NULL)
    {
      owner->stopped = 1;
    }
  }
  else
  {
    owner->live_bytes -= (uint64_t)size;
  }
  free(header);
}

size_t stp_lra_imath_allocation_alignment(void)
{
  return offsetof(stp_lra_imath_alignment_probe, value);
}

#if defined(STP_LRA_TEST_FAULT_INJECTION)
void stp_lra_imath_test_fail_nth(uint64_t allocation_index)
{
  fault_index = allocation_index;
  fault_attempts = 0;
}

void stp_lra_imath_test_disable_failures(void)
{
  fault_index = UINT64_MAX;
  fault_attempts = 0;
}

uint64_t stp_lra_imath_test_allocation_attempts(void)
{
  return fault_attempts;
}
#endif
