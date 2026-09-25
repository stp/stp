#ifndef STP_LRA_STORAGE_GROWTH_H
#define STP_LRA_STORAGE_GROWTH_H

#include <algorithm>
#include <cstddef>

namespace stp::lra::detail
{

// Reserve so that a later growth to `count` elements cannot reallocate,
// doubling the capacity whenever it does have to grow, so that growing one
// element at a time costs amortised constant time per element.
//
// This is the strong exception guarantee without the copy. Every container in
// the exact core used to grow by copying itself, appending to the copy and
// swapping the copy in, so that a failed allocation left the original
// untouched -- and so that adding the n-th variable copied the n-1 before it,
// which is quadratic in the variables, and cubic where each one is a
// polynomial of exact rationals. Reserving is the only step that can fail, and
// std::vector::reserve leaves the vector unchanged when it does; the growth
// that follows, within capacity already held, cannot fail for the element
// types these containers hold, or has the strong guarantee on its own where an
// element copy can throw.
template <class Vector>
void reserveFor(Vector& vector, std::size_t count)
{
  if (count <= vector.capacity())
    return;
  vector.reserve(std::max(count, vector.capacity() * 2U));
}

template <class Vector>
void reserveForOneMore(Vector& vector)
{
  reserveFor(vector, vector.size() + 1U);
}

}  // namespace stp::lra::detail

#endif
