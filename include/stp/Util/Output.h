#ifndef STP_UTIL_OUTPUT_H
#define STP_UTIL_OUTPUT_H

#include "stp/AST/AST.h"
#include <functional>
#include <string_view>

namespace stp { namespace api { namespace detail {
// Where the text the engine writes while it works goes. The engine prints to
// std::cout (responses, answers, what the printing options print) and to
// std::cerr (statistics, warnings, "Fatal Error:" reports); while a route is
// alive on a thread, that thread's writes to either stream go to the route's
// sinks instead of the process's streams, and a null or empty sink drops
// them. An empty chunk to `out` is a flush: the text so far is complete.
// Output.cpp installs the streams' dispatching buffers the first time a route
// is made; a thread with no route writes to the process's streams as before.
struct OutputSinks
{
  const std::function<void(std::string_view)>* out = nullptr;
  const std::function<void(std::string_view)>* err = nullptr;
  // Told of a fatal error the engine reports, before anything unwinds
  // (Solver::set_fatal_error_handler).
  const std::function<void(std::string_view)>* fatal = nullptr;
};
// Every write dropped: what an API call that is no solver's work routes to.
extern const OutputSinks kNoOutput;
const OutputSinks* current_output_route() noexcept;
class OutputRoute
{
public:
  explicit OutputRoute(const OutputSinks* sinks, bool preserveFatalObserver = false);
  ~OutputRoute();
  OutputRoute(const OutputRoute&) = delete;
  OutputRoute& operator=(const OutputRoute&) = delete;

private:
  const OutputSinks* saved_;
  stp::FatalErrorObserver saved_observer_;
  void* saved_opaque_;
};


} } }
#endif
