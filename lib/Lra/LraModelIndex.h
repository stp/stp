#ifndef STP_LRA_MODEL_INDEX_H
#define STP_LRA_MODEL_INDEX_H

#include "LraSolveContext.h"

#include <algorithm>
#include <string>
#include <vector>

namespace stp::lra {

// A temporary, checked index at a model boundary. Sort pointers, preserving the
// owning vector's order and comparing complete identities (including domain or
// generation). Rebuild at each boundary rather than trusting a cached registry
// index after the private model/snapshot could have been corrupted.
template <class Entry, class Id>
class LraModelIndex final
{
 public:
  LraModelIndex(std::vector<Entry> const& entries, Id Entry::*member,
                NumberLimits limits, char const* description)
      : member_(member), description_(description)
  {
    if (entries.size() > ordered_.max_size() ||
        entries.size() > limits.maximum_allocation_bytes / sizeof(Entry const*))
      throw SolveContextFailure(SolveContextFailureKind::ResourceLimit,
                                std::string(description_) + " index allocation limit");
    ordered_.reserve(entries.size());
    for (Entry const& entry : entries)
      ordered_.push_back(&entry);
    std::sort(ordered_.begin(), ordered_.end(), [member](auto lhs, auto rhs) {
      return lhs->*member < rhs->*member;
    });
    for (std::size_t i = 1; i < ordered_.size(); ++i)
      if (ordered_[i - 1]->*member_ == ordered_[i]->*member_)
        throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                  std::string("duplicate ") + description_);
  }

  Entry const& at(Id id) const
  {
    auto const found = std::lower_bound(
        ordered_.begin(), ordered_.end(), id, [this](auto entry, Id key) {
          return entry->*member_ < key;
        });
    if (found == ordered_.end() || !((*found)->*member_ == id))
      throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                std::string("missing ") + description_);
    return **found;
  }

 private:
  Id Entry::*member_;
  char const* description_;
  std::vector<Entry const*> ordered_;
};

}  // namespace stp::lra

#endif
