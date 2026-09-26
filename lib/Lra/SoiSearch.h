#ifndef STP_LRA_SOI_SEARCH_H
#define STP_LRA_SOI_SEARCH_H

#include <algorithm>
#include <cmath>
#include <cstdint>
#include <optional>
#include <type_traits>
#include <vector>

namespace stp::lra
{

// Minimize the sum of bound violations along one nonbasic direction.
// Each crossed lower/upper bound increases the derivative by |a|. Sorting
// those breakpoints finds the minimum in O(k log k), including a possible
// stop at the nonbasic variable's own bound. Value carries symbolic epsilon;
// Coefficient is a rational or a double. No feasibility verdict comes from
// this search: the ordinary simplex remains responsible for conflicts.
// After the sum-of-infeasibilities simplex of King, Barrett & Dutertre,
// "Simplex with Sum of Infeasibilities for SMT", FMCAD 2013.
template <class Value, class Coefficient>
class SoiLineSearch final
{
public:
  static constexpr std::uint32_t no_row = 0xffffffffU;
  struct Move
  {
    Value gain;
    Value target;
    std::uint32_t row;
  };

  void addBound(Value const& value, Value const& bound,
                Coefficient const& direction, bool lower,
                std::uint32_t row, std::size_t row_size)
  {
    Coefficient const zero{};
    if (direction == zero)
      return;
    bool const positive = zero < direction;
    if (lower ? (value < bound || (value == bound && !positive))
              : (bound < value || (value == bound && positive)))
      slope_ = lower ? slope_ - direction : slope_ + direction;
    Value distance = (bound - value) / direction;
    if (!finite(distance))
      usable_ = false;
    else if (Value{} < distance)
      events_.push_back(Event{std::move(distance),
                              positive ? direction : -direction,
                              bound, row, row_size});
  }

  void limit(Value distance, Value const& bound)
  {
    if (!finite(distance) || !(Value{} < distance))
      usable_ = false;
    else
      events_.push_back(Event{std::move(distance), Coefficient{}, bound,
                              no_row, 0});
  }

  std::optional<Move> best()
  {
    if constexpr (std::is_floating_point_v<Coefficient>)
      usable_ &= std::isfinite(slope_);
    if (!usable_ || !(slope_ < Coefficient{}))
      return std::nullopt;
    std::sort(events_.begin(), events_.end(), [](Event const& a, Event const& b) {
      if (!(a.distance == b.distance))
        return a.distance < b.distance;
      if (a.row_size != b.row_size)
        return a.row_size < b.row_size; // prefer a bound flip to a pivot
      return a.row < b.row;
    });
    Value previous{}, gain{};
    std::optional<Move> result;
    for (std::size_t i = 0; i < events_.size();)
    {
      Event const& event = events_[i];
      gain = gain - (event.distance - previous) * slope_;
      if (!finite(gain))
        return std::nullopt;
      if (Value{} < gain && (!result || result->gain < gain))
        result = Move{gain, event.target, event.row};
      previous = event.distance;
      bool at_limit = false;
      do
      {
        at_limit |= events_[i].row == no_row;
        slope_ = slope_ + events_[i].slope_change;
        ++i;
      } while (i < events_.size() && events_[i].distance == previous);
      if (at_limit || !(slope_ < Coefficient{}))
        break;
    }
    return result;
  }

private:
  static bool finite(Value const& value)
  {
    if constexpr (std::is_floating_point_v<Coefficient>)
      return std::isfinite(value.value) && std::isfinite(value.delta);
    else
      return true;
  }
  struct Event
  {
    Value distance;
    Coefficient slope_change;
    Value target;
    std::uint32_t row;
    std::size_t row_size;
  };
  Coefficient slope_{};
  bool usable_ = true;
  std::vector<Event> events_;
};

} // namespace stp::lra
#endif
