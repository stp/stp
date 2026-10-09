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

#include "Source.h"
#include <algorithm>
#include <cerrno>
#include <cstring>
#include <fcntl.h>
#include <istream>
#include <poll.h>
#include <stdexcept>
#include <streambuf>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

namespace stpp
{
namespace
{
[[noreturn]] void too_large(std::uint64_t limit)
{
  throw std::runtime_error(
      "the input exceeds " + std::to_string(limit >> 20) +
      " MiB, the per-process memory limit (--worker-memory-mib): no process "
      "could parse it");
}
std::string why()
{
  return strerror(errno);
}
std::size_t pages(std::uint64_t bytes)
{
  const auto page = static_cast<std::uint64_t>(sysconf(_SC_PAGESIZE));
  return static_cast<std::size_t>((bytes + page - 1) / page * page);
}
// A read-only view of bytes in memory as a stream, so that STP's parser
// reads the script where it is instead of copying it.
struct View final : std::streambuf
{
  explicit View(std::string_view text)
  {
    char* begin = const_cast<char*>(text.data());
    setg(begin, begin, begin + text.size());
  }
};
} // namespace

Source::~Source()
{
  release();
}
void Source::release()
{
  if (map)
    munmap(map, mapped);
  map = nullptr;
  size = mapped = 0;
  std::string().swap(heap);
}
std::uint64_t input_limit(const Options& o)
{
  return (o.worker_mib ? o.worker_mib : 16384) * 1024 * 1024;
}
bool read_source(const std::string& path, Source& out, std::uint64_t limit,
                 double deadline, const volatile int& stop)
{
  const bool standard = path == "-";
  int fd = standard ? STDIN_FILENO
                    : open(path.c_str(), O_RDONLY | O_CLOEXEC | O_NONBLOCK);
  if (fd < 0)
    throw std::runtime_error("cannot open input: " + path + ": " + why());
  if (standard && isatty(fd))
    throw std::runtime_error("no input file, and stdin is a terminal: give a "
                             "file, or pipe the query in");
  struct Close
  {
    int fd;
    bool own;
    ~Close()
    {
      if (own)
        close(fd);
    }
  } closer{fd, !standard};
  struct stat st{};
  if (fstat(fd, &st))
    throw std::runtime_error("cannot read input: " + why());
  // A regular file of known size is mapped read-only: one mapping, nothing
  // copied, and the bytes are read in only as the parse reaches them.
  if (S_ISREG(st.st_mode) && st.st_size > 0)
  {
    if (std::uint64_t(st.st_size) > limit)
      too_large(limit);
    void* map = mmap(nullptr, static_cast<std::size_t>(st.st_size), PROT_READ,
                     MAP_PRIVATE, fd, 0);
    if (map == MAP_FAILED)
      throw std::runtime_error("cannot map the input: " + why());
    out.map = map;
    out.size = out.mapped = static_cast<std::size_t>(st.st_size);
    return true;
  }
  // Anything else -- a pipe, a FIFO, a file whose size the system does not
  // know -- is read into anonymous memory that doubles in place (mremap), up
  // to a page past the limit: an input over the limit ends here, before it
  // costs more.
  void* base = nullptr;
  std::size_t capacity = 0, size = 0;
  struct Spool
  {
    void*& base;
    std::size_t& capacity;
    bool kept = false;
    ~Spool()
    {
      if (!kept && base)
        munmap(base, capacity);
    }
  } spool{base, capacity};
  const std::size_t most = pages(limit + 1), chunk = std::size_t(1) << 20;
  for (;;)
  {
    if (stop || (deadline && now() >= deadline))
      return false;
    if (size == capacity)
    {
      const std::size_t want =
          std::min(most, capacity ? 2 * capacity : pages(chunk));
      void* grown = capacity ? mremap(base, capacity, want, MREMAP_MAYMOVE)
                             : mmap(nullptr, want, PROT_READ | PROT_WRITE,
                                    MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
      if (grown == MAP_FAILED)
        throw std::runtime_error("cannot hold the input (" +
                                 std::to_string(size >> 20) +
                                 " MiB read): " + why());
      base = grown;
      capacity = want;
    }
    pollfd p{fd, POLLIN, 0};
    const int ready = poll(&p, 1, 10);
    if (ready < 0 && errno != EINTR)
      throw std::runtime_error("input poll failed: " + why());
    if (ready <= 0)
      continue;
    const auto n = read(fd, static_cast<char*>(base) + size,
                        std::min(capacity - size, chunk));
    if (n < 0 && (errno == EINTR || errno == EAGAIN || errno == EWOULDBLOCK))
      continue;
    if (n < 0)
      throw std::runtime_error("input read failed: " + why());
    if (!n)
      break;
    size += std::size_t(n);
    if (size > limit)
      too_large(limit);
  }
  if (!size)
    return true;
  // What was read stays, read-only; the rest of the mapping goes.
  const std::size_t keep = pages(size);
  if (keep < capacity)
  {
    void* shrunk = mremap(base, capacity, keep, 0);
    if (shrunk != MAP_FAILED)
      capacity = keep;
  }
  mprotect(base, capacity, PROT_READ);
  out.map = base;
  out.size = size;
  out.mapped = capacity;
  spool.kept = true;
  return true;
}
std::string parse_query(stp::Solver& solver, Source& source)
{
  // The library refuses a NUL in a stream only when its reader reaches it,
  // after what comes before it has been parsed. Refusing it here keeps the
  // refusal ahead of the parse, and names its offset.
  if (const auto nul = source.text().find('\0'); nul != std::string_view::npos)
    throw std::runtime_error(
        "unsupported/invalid SMT-LIB: the input holds a NUL byte at offset " +
        std::to_string(nul));
  {
    View view(source.text());
    std::istream in(&view);
    solver.parse(in, stp::Format::SMTLIB2, stp::ParseMode::SINGLE_QUERY);
  }
  source.release();
  return solver.declared_logic();
}
void admit_logic(const std::string& logic, bool theories)
{
  const bool theory = logic == "QF_ABV" || logic == "QF_FP" ||
                      logic == "QF_BVFP" || logic == "QF_ABVFP";
  if (!logic.empty() && logic != "QF_BV" && !(theories && theory))
    throw std::runtime_error(
        "unsupported/invalid SMT-LIB: " +
        std::string(theories ? "logic must be QF_BV, QF_ABV, QF_FP, QF_BVFP "
                               "or QF_ABVFP"
                             : "logic must be QF_BV") +
        ", not " + logic);
}
} // namespace stpp
