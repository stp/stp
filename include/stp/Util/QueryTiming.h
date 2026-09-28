#ifndef STP_QUERY_TIMING_H
#define STP_QUERY_TIMING_H

#include <array>
#include <chrono>
#include <cstdint>
#include <ostream>

namespace stp
{

enum class QueryPhase
{
  Other,
  BitBlasting,
  CNFConversion,
  ClauseLoading,
  EncodingOther,
  EncodingCleanup,
  LraCleanup,
  SolverCleanup,
  QueryCleanup,
  Count
};

// Exclusive wall times: nested phases pause their parent, so the buckets
// sum to the query wall time. Parsing happens before this query-local clock.
class QueryTiming final
{
public:
  using Clock = std::chrono::steady_clock;
  using Now = Clock::time_point (*)();
  static constexpr unsigned count = static_cast<unsigned>(QueryPhase::Count);
  using Totals = std::array<std::uint64_t, count>;

  explicit QueryTiming(Clock::time_point started, Now now = Clock::now)
      : last_(started), now_(now) {}

  QueryPhase enter(QueryPhase phase)
  {
    account();
    const auto previous = phase_;
    phase_ = phase;
    return previous;
  }

  Totals totals()
  {
    account();
    return times_;
  }

  void print(std::ostream& out)
  {
    const auto values = totals();
    std::uint64_t total = 0;
    for (auto value : values)
      total += value;
    static const char* names[] = {
        "other", "bitblast", "cnf", "clauses", "encoding_other",
        "encoding_cleanup", "lra_cleanup", "solver_cleanup", "query_cleanup"};
    out << "Query phases: total_ns=" << total;
    for (unsigned i = 0; i != count; ++i)
      out << ' ' << names[i] << "_ns=" << values[i];
    out << '\n';
  }

private:
  void account()
  {
    const auto current = now_();
    times_[static_cast<unsigned>(phase_)] += static_cast<std::uint64_t>(
        std::chrono::duration_cast<std::chrono::nanoseconds>(current - last_).count());
    last_ = current;
  }
  Clock::time_point last_;
  Now now_;
  QueryPhase phase_ = QueryPhase::Other;
  Totals times_{};
};

class QueryPhaseScope final
{
public:
  QueryPhaseScope(QueryTiming* timing, QueryPhase phase)
      : timing_(timing), previous_(timing ? timing->enter(phase) : phase) {}
  ~QueryPhaseScope() { finish(); }
  void finish()
  {
    if (timing_)
    {
      timing_->enter(previous_);
      timing_ = nullptr;
    }
  }
  QueryPhaseScope(const QueryPhaseScope&) = delete;
  QueryPhaseScope& operator=(const QueryPhaseScope&) = delete;
private:
  QueryTiming* timing_;
  QueryPhase previous_;
};

// Declare after the owners whose destruction is to be measured, inside a
// QueryPhaseScope. On return/unwind, those owners run in the cleanup phase;
// the enclosing scope restores the caller's phase after they are destroyed.
class QueryCleanupOnExit final
{
public:
  QueryCleanupOnExit(QueryTiming* timing, QueryPhase phase)
      : timing_(timing), phase_(phase) {}
  ~QueryCleanupOnExit() { if (timing_) timing_->enter(phase_); }
  QueryCleanupOnExit(const QueryCleanupOnExit&) = delete;
  QueryCleanupOnExit& operator=(const QueryCleanupOnExit&) = delete;
private:
  QueryTiming* timing_;
  QueryPhase phase_;
};

template <class T> struct QueryTimedDelete
{
  QueryTiming* timing;
  QueryPhase phase;
  void operator()(T* pointer) const
  {
    QueryPhaseScope scope(timing, phase);
    delete pointer;
  }
};

class QueryTimingReport final
{
public:
  QueryTimingReport(QueryTiming*& slot, QueryTiming* timing, std::ostream& out)
      : slot_(slot), saved_(slot), timing_(timing), out_(out) { slot_ = timing; }
  ~QueryTimingReport()
  {
    slot_ = saved_;
    // Diagnostics must not change the result, including during unwinding.
    try { if (timing_) timing_->print(out_); } catch (...) {}
  }
  QueryTimingReport(const QueryTimingReport&) = delete;
  QueryTimingReport& operator=(const QueryTimingReport&) = delete;
private:
  QueryTiming*& slot_;
  QueryTiming* saved_;
  QueryTiming* timing_;
  std::ostream& out_;
};

} // namespace stp
#endif
