# Prepare the exact pinned unordered_dense header used by STP.  STP's
# allocation-failure contract needs two narrowly scoped fixes: a non-allocating
# same-allocator swap and access to the container's integral insertion
# threshold.  Generate the derived header in the build tree so the current
# upstream FetchContent dependency remains authoritative and pristine.

set(_stp_unordered_dense_source_header
    "${unordereddense_SOURCE_DIR}/include/ankerl/unordered_dense.h")
set(_stp_unordered_dense_source_sha256
    "b5f67c6895a58e059273cf24bae16cb07e6c72f0e3f88bbebecaddd987b102b3")

if(NOT EXISTS "${_stp_unordered_dense_source_header}")
  message(FATAL_ERROR
      "Pinned ankerl::unordered_dense header is absent: "
      "${_stp_unordered_dense_source_header}")
endif()
file(SHA256 "${_stp_unordered_dense_source_header}"
     _stp_unordered_dense_observed_sha256)
if(NOT _stp_unordered_dense_observed_sha256 STREQUAL
       _stp_unordered_dense_source_sha256)
  message(FATAL_ERROR
      "ankerl::unordered_dense ${UNORDERED_DENSE_VERSION} header identity "
      "mismatch: expected ${_stp_unordered_dense_source_sha256}, observed "
      "${_stp_unordered_dense_observed_sha256}")
endif()

file(READ "${_stp_unordered_dense_source_header}"
     _stp_unordered_dense_content)

set(_stp_unordered_dense_swap_anchor [=[
    void swap(table& other) noexcept(noexcept(std::is_nothrow_swappable_v<value_container_type> &&
                                              std::is_nothrow_swappable_v<Hash> && std::is_nothrow_swappable_v<KeyEqual>)) {
        using std::swap;
        swap(other, *this);
    }
]=])
set(_stp_unordered_dense_swap_replacement [=[
    void swap(table& other) noexcept(noexcept(std::is_nothrow_swappable_v<value_container_type> &&
                                              std::is_nothrow_swappable_v<Hash> && std::is_nothrow_swappable_v<KeyEqual>)) {
        using std::swap;
        if (get_allocator() == other.get_allocator()) {
            // Swapping the table object through std::swap selects the generic
            // move-construction path. table's move assignment reinitializes
            // the moved-from bucket array, which allocates and can therefore
            // terminate inside this noexcept function. Swap the complete
            // representation directly when the allocators agree; this is the
            // ordinary/default-allocator case and performs no allocation.
            swap(m_values, other.m_values);
            swap(m_buckets, other.m_buckets);
            swap(m_max_bucket_capacity, other.m_max_bucket_capacity);
            swap(m_max_load_factor, other.m_max_load_factor);
            swap(m_hash, other.m_hash);
            swap(m_equal, other.m_equal);
            swap(m_shifts, other.m_shifts);
            return;
        }
        swap(other, *this);
    }
]=])

set(_stp_unordered_dense_bucket_anchor [=[
    auto bucket_count() const noexcept -> size_t { // NOLINT(modernize-use-nodiscard)
        return m_buckets.size();
    }

    static constexpr auto max_bucket_count() noexcept -> size_t { // NOLINT(modernize-use-nodiscard)
]=])
set(_stp_unordered_dense_bucket_replacement [=[
    auto bucket_count() const noexcept -> size_t { // NOLINT(modernize-use-nodiscard)
        return m_buckets.size();
    }

    // STP's hash-cons tables need to know whether the next insert can rebuild
    // the bucket array. Expose the container's already-computed integral
    // threshold so callers never reconstruct it through the floating
    // load-factor API.
    [[nodiscard]] auto stp_insertion_may_rehash() const noexcept -> bool {
        return 0 == bucket_count() ||
               size() >= static_cast<size_t>(m_max_bucket_capacity);
    }

    static constexpr auto max_bucket_count() noexcept -> size_t { // NOLINT(modernize-use-nodiscard)
]=])

foreach(_stp_anchor IN ITEMS swap bucket)
  string(FIND "${_stp_unordered_dense_content}"
         "${_stp_unordered_dense_${_stp_anchor}_anchor}" _stp_anchor_first)
  string(FIND "${_stp_unordered_dense_content}"
         "${_stp_unordered_dense_${_stp_anchor}_anchor}" _stp_anchor_last
         REVERSE)
  if(_stp_anchor_first LESS 0 OR NOT _stp_anchor_first EQUAL _stp_anchor_last)
    message(FATAL_ERROR
        "Pinned unordered_dense ${_stp_anchor} patch anchor is not unique")
  endif()
  string(REPLACE "${_stp_unordered_dense_${_stp_anchor}_anchor}"
                 "${_stp_unordered_dense_${_stp_anchor}_replacement}"
                 _stp_unordered_dense_content
                 "${_stp_unordered_dense_content}")
endforeach()

set(STP_UNORDERED_DENSE_INCLUDE_DIR
    "${PROJECT_BINARY_DIR}/generated-extlib-unordered-dense/include")
set(_stp_unordered_dense_output_header
    "${STP_UNORDERED_DENSE_INCLUDE_DIR}/ankerl/unordered_dense.h")
file(MAKE_DIRECTORY "${STP_UNORDERED_DENSE_INCLUDE_DIR}/ankerl")
file(WRITE "${_stp_unordered_dense_output_header}"
     "${_stp_unordered_dense_content}")

unset(_stp_unordered_dense_content)
unset(_stp_unordered_dense_observed_sha256)
unset(_stp_unordered_dense_output_header)
unset(_stp_unordered_dense_source_header)
unset(_stp_unordered_dense_source_sha256)
unset(_stp_unordered_dense_swap_anchor)
unset(_stp_unordered_dense_swap_replacement)
unset(_stp_unordered_dense_bucket_anchor)
unset(_stp_unordered_dense_bucket_replacement)
unset(_stp_anchor)
unset(_stp_anchor_first)
unset(_stp_anchor_last)
