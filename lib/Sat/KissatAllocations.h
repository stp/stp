/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: October, 2026
 *
Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
********************************************************************/

#ifndef STP_SAT_KISSATALLOCATIONS_H
#define STP_SAT_KISSATALLOCATIONS_H

#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <limits>
#include <new>

namespace stp
{
namespace detail
{
// A failed C allocation must reach STP's RESOURCE handler. Own every block,
// including temporary inprocessing allocations, so an interrupted allocation
// can discard the partial C solver without walking its unfinished structures.
struct KissatAllocations
{
  // Keep ownership beside the payload, without another allocation or a hash
  // lookup. Keep the header and payload aligned for the callback's scalars.
  struct alignas(void*) alignas(double) alignas(std::uint64_t) Block
  {
    Block* previous;
    Block* next;
  };
  Block* blocks = nullptr;
  bool failed = false;

  KissatAllocations() = default;
  KissatAllocations(const KissatAllocations&) = delete;
  KissatAllocations& operator=(const KissatAllocations&) = delete;

  ~KissatAllocations()
  {
    while (blocks)
    {
      Block* block = blocks;
      blocks = block->next;
      std::free(block);
    }
  }

  static std::size_t storageSize(KissatAllocations& self, std::size_t bytes)
  {
    if (bytes > std::numeric_limits<std::size_t>::max() - sizeof(Block))
    {
      self.failed = true;
      throw std::bad_alloc();
    }
    return sizeof(Block) + bytes;
  }

  static void* allocate(void* state, std::size_t bytes)
  {
    auto& self = *static_cast<KissatAllocations*>(state);
    void* storage = std::malloc(storageSize(self, bytes));
    if (!storage)
    {
      self.failed = true;
      throw std::bad_alloc();
    }
    Block* block = new (storage) Block{nullptr, self.blocks};
    if (block->next)
      block->next->previous = block;
    self.blocks = block;
    return block + 1;
  }

  static void* resize(void* state, void* ptr, std::size_t bytes)
  {
    if (!ptr)
      return allocate(state, bytes);
    auto& self = *static_cast<KissatAllocations*>(state);
    Block* old = static_cast<Block*>(ptr) - 1;
    Block* previous = old->previous;
    Block* next = old->next;
    void* storage = std::realloc(old, storageSize(self, bytes));
    if (!storage)
    {
      // A failed resize leaves the old block and its ownership links intact.
      self.failed = true;
      throw std::bad_alloc();
    }
    Block* block = new (storage) Block{previous, next};
    if (previous)
      previous->next = block;
    else
      self.blocks = block;
    if (next)
      next->previous = block;
    return block + 1;
  }

  static void deallocate(void* state, void* ptr)
  {
    if (!ptr)
      return;
    auto& self = *static_cast<KissatAllocations*>(state);
    Block* block = static_cast<Block*>(ptr) - 1;
    if (block->previous)
      block->previous->next = block->next;
    else
      self.blocks = block->next;
    if (block->next)
      block->next->previous = block->previous;
    std::free(block);
  }
};

} // namespace detail
} // namespace stp

#endif
