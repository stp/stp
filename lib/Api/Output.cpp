/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: September, 2026
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

// Output.cpp -- where the text the engine prints goes (OutputRoute in
// Internal.h).
//
// The engine prints with std::cout and std::cerr. The first route made puts
// a dispatching buffer in front of each stream's own buffer: on a thread with
// no route alive, a write goes to the stream's own buffer as it always did;
// on a thread with a route, it goes to that route's sink, or nowhere. The
// dispatching buffers keep no buffer of their own, so the text reaches a
// sink in the order and in the pieces the engine wrote it, and a stream's
// flush (std::endl, std::flush, and std::cerr's flush of the std::cout it is
// tied to) reaches the output sink as an empty chunk.

#include "Internal.h"

#include <iostream>
#include <map>
#include <mutex>
#include <streambuf>
#include <utility>

namespace stp
{
namespace api
{
namespace detail
{

const OutputSinks kNoOutput{};

namespace
{

thread_local const OutputSinks* t_route = nullptr;
thread_local int t_callback_depth = 0;

// A sink that writes to std::cout or std::cerr itself finds no route while it
// runs, and so reaches the process's stream rather than itself.
struct Unrouted
{
  const OutputSinks* saved;
  Unrouted() noexcept : saved(t_route) { t_route = nullptr; }
  ~Unrouted() { t_route = saved; }
  Unrouted(const Unrouted&) = delete;
  Unrouted& operator=(const Unrouted&) = delete;
};

// A sink's exception is dropped: thrown through a stream, it would leave the
// process's std::cout or std::cerr failed for every later write.
void deliver(const std::function<void(std::string_view)>* sink, std::string_view text) noexcept
{
  if (sink == nullptr || !*sink)
    return;
  Unrouted unrouted;
  const InCallback callback;
  try
  {
    (*sink)(text);
  }
  catch (...)
  {
  }
}

class DispatchBuf final : public std::streambuf
{
public:
  DispatchBuf(std::streambuf* original, bool diagnostic) noexcept
      : original_(original), diagnostic_(diagnostic)
  {
  }

protected:
  int_type overflow(int_type c) override
  {
    if (traits_type::eq_int_type(c, traits_type::eof()))
      return traits_type::not_eof(c);
    const char ch = traits_type::to_char_type(c);
    return write(&ch, 1) == 1 ? c : traits_type::eof();
  }

  std::streamsize xsputn(const char* s, std::streamsize n) override { return write(s, n); }

  int sync() override
  {
    const OutputSinks* route = t_route;
    if (route == nullptr)
      return original_ == nullptr ? 0 : original_->pubsync();
    if (!diagnostic_)
      deliver(route->out, std::string_view());
    return 0;
  }

private:
  std::streamsize write(const char* s, std::streamsize n)
  {
    const OutputSinks* route = t_route;
    if (route == nullptr)
      return original_ == nullptr ? n : original_->sputn(s, n);
    if (n > 0)
      deliver(diagnostic_ ? route->err : route->out,
              std::string_view(s, static_cast<std::size_t>(n)));
    return n;
  }

  std::streambuf* original_;
  bool diagnostic_;
};

// A dispatching buffer in front of the stream's current one, unless one is
// there already. An application may swap the stream's buffer after the
// library first ran -- a scoped redirection of std::cout, say -- and the
// engine's output would then reach that buffer rather than the solver's
// sinks; so every route checks, and puts a dispatching buffer in front of
// the new one, which unrouted writes still reach. One per buffer seen,
// reused, and never freed: the streams may write through them until the
// process ends. Called with install_dispatch's lock held.
void ensure_dispatch(std::ostream& stream, bool diagnostic)
{
  static auto* const made = new std::map<std::pair<std::streambuf*, bool>, DispatchBuf*>();
  std::streambuf* const current = stream.rdbuf();
  if (dynamic_cast<DispatchBuf*>(current) != nullptr)
    return;
  DispatchBuf*& wrapper = (*made)[std::make_pair(current, diagnostic)];
  if (wrapper == nullptr)
    wrapper = new DispatchBuf(current, diagnostic);
  stream.rdbuf(wrapper);
}

// The check as well as the change under the lock: a route on another thread
// may be putting a dispatching buffer in front of either stream, and reading
// a stream's buffer while it does is a data race -- on the first routes of
// managers made on several threads at once, say.
void install_dispatch()
{
  static std::mutex lock;
  std::lock_guard<std::mutex> hold(lock);
  ensure_dispatch(std::cout, false);
  ensure_dispatch(std::cerr, true);
}

void observe_fatal(const char* str, void* opaque)
{
  const OutputSinks* route = static_cast<const OutputSinks*>(opaque);
  if (route == nullptr || route->fatal == nullptr || !*route->fatal)
    return;
  // The engine is in the middle of failing: nothing may unwind from here
  // but the failure itself (deliver drops what the handler throws).
  deliver(route->fatal, str == nullptr ? "" : str);
}

} // namespace

const OutputSinks* current_output_route() noexcept
{
  return t_route;
}

OutputRoute::OutputRoute(const OutputSinks* sinks, bool preserveFatalObserver)
    : saved_(t_route)
{
  install_dispatch();
  saved_observer_ = stp::GetFatalErrorObserver(&saved_opaque_);
  t_route = sinks;
  if (!preserveFatalObserver)
    stp::SetFatalErrorObserver(&observe_fatal, const_cast<OutputSinks*>(sinks));
}

OutputRoute::~OutputRoute()
{
  t_route = saved_;
  stp::SetFatalErrorObserver(saved_observer_, saved_opaque_);
}

int& callback_depth() noexcept
{
  return t_callback_depth;
}

} // namespace detail
} // namespace api
} // namespace stp
