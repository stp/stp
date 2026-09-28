#ifndef STP_PREPARATION_CONTROL_H
#define STP_PREPARATION_CONTROL_H

#include <chrono>
#include <cstdint>
#include <exception>

namespace stp
{

enum class PreparationStage
{
  Boundary,
  UFLowering,
  LraPresolve,
  LraPreregistration,
  LraRegistry,
  LraCore,
  Encoding,
  BitBlasting,
  CNFConversion,
  ClauseLoading,
  RefinementEncoding
};

inline const char* preparationStageName(PreparationStage stage)
{
  switch (stage)
  {
    case PreparationStage::Boundary: return "boundary";
    case PreparationStage::UFLowering: return "uf-lowering";
    case PreparationStage::LraPresolve: return "lra-presolve";
    case PreparationStage::LraPreregistration: return "lra-preregistration";
    case PreparationStage::LraRegistry: return "lra-registry";
    case PreparationStage::LraCore: return "lra-core";
    case PreparationStage::Encoding: return "encoding";
    case PreparationStage::BitBlasting: return "bitblasting";
    case PreparationStage::CNFConversion: return "cnf-conversion";
    case PreparationStage::ClauseLoading: return "clause-loading";
    case PreparationStage::RefinementEncoding: return "refinement-encoding";
  }
  return "unknown";
}

class PreparationInterrupted final : public std::exception
{
public:
  using Clock = std::chrono::steady_clock;
  PreparationInterrupted(PreparationStage stage, Clock::time_point noticed)
      : stage(stage), noticed(noticed) {}
  const char* what() const noexcept override
  {
    return "query deadline reached during preparation";
  }
  PreparationStage stage;
  Clock::time_point noticed;
};

// Query-local, cooperative cancellation. An optional outer observer can
// impose an earlier stop (and makes mid-stage cancellation deterministic in
// tests). Every replacement backend/preparation attempt uses the same owner.
class PreparationControl final
{
public:
  using Clock = PreparationInterrupted::Clock;
  using Observer = bool (*)(void*, PreparationStage);

  explicit PreparationControl(
      Clock::time_point deadline = Clock::time_point::max(),
      const PreparationControl* outer = nullptr,
      Observer observer = nullptr, void* opaque = nullptr)
      : deadline_(deadline), outer_(outer), observer_(observer), opaque_(opaque)
  {
  }

  void check(PreparationStage stage) const
  {
    if (stopped_)
      throw PreparationInterrupted(stage_, noticed_);
    if (outer_)
      outer_->check(stage);
    if ((observer_ && observer_(opaque_, stage)) ||
        (deadline_ != Clock::time_point::max() && Clock::now() >= deadline_))
    {
      stopped_ = true;
      stage_ = stage;
      noticed_ = Clock::now();
      throw PreparationInterrupted(stage_, noticed_);
    }
  }

private:
  Clock::time_point deadline_;
  const PreparationControl* outer_;
  Observer observer_;
  void* opaque_;
  mutable bool stopped_ = false;
  mutable PreparationStage stage_ = PreparationStage::Boundary;
  mutable Clock::time_point noticed_{};
};

class PreparationScope final
{
public:
  PreparationScope(const PreparationControl*& slot,
                   const PreparationControl& control)
      : slot_(slot), saved_(slot) { slot_ = &control; }
  ~PreparationScope() { slot_ = saved_; }
  PreparationScope(const PreparationScope&) = delete;
  PreparationScope& operator=(const PreparationScope&) = delete;
private:
  const PreparationControl*& slot_;
  const PreparationControl* saved_;
};

// Check entry and each 256 work items. Call check() at stage boundaries too;
// polling is never used in rollback or destruction, which must finish.
class PreparationPoller final
{
public:
  PreparationPoller(const PreparationControl* control, PreparationStage stage)
      : control_(control), stage_(stage) { check(); }
  void operator()()
  {
    if (control_ && (++work_ & 255u) == 0)
      control_->check(stage_);
  }
  void check() const
  {
    if (control_)
      control_->check(stage_);
  }
private:
  const PreparationControl* control_;
  PreparationStage stage_;
  std::uint32_t work_ = 0;
};

// Shared by the three circuit managers. Only batch preparation installs a
// control; other users retain the default null control and their own budgets.
class EncodingPreparation
{
public:
  void setPreparationControl(const PreparationControl* control)
  {
    control_ = control;
    poll_ = PreparationPoller(control, PreparationStage::BitBlasting);
  }
  const PreparationControl* preparationControl() const { return control_; }
  void pollPreparation() const { poll_(); }
private:
  const PreparationControl* control_ = nullptr;
  mutable PreparationPoller poll_{nullptr, PreparationStage::BitBlasting};
};

} // namespace stp
#endif
