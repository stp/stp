// -*- c++ -*-
/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: August, 2026
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#ifndef INCREMENTALPOLICY_H_
#define INCREMENTALPOLICY_H_

namespace stp
{

// Policy decisions which are not needed for the correctness of the
// persistent assumption solver. Keeping them behind one immutable profile
// makes the minimal core executable on its own: root encodings, SAT
// assumptions, theory refinement, model reconstruction and memory-relief
// epoch rotation remain active, while fitted workload heuristics do not.
class IncrementalPolicy
{
  bool coreOnlyValue;

public:
  explicit IncrementalPolicy(bool coreOnly = false)
      : coreOnlyValue(coreOnly)
  {
  }

  bool coreOnly() const { return coreOnlyValue; }

  bool crossLevelPropagation() const { return !coreOnlyValue; }
  bool semanticPreprocessing() const { return !coreOnlyValue; }
  bool firstSolveShortcuts() const { return !coreOnlyValue; }
  bool unitPromotion() const { return !coreOnlyValue; }
  bool adaptiveBackendConfiguration() const { return !coreOnlyValue; }
  bool aggregateLevelAssumptions() const { return !coreOnlyValue; }
  bool retractionSearchHints() const { return !coreOnlyValue; }

  // Resource reclamation is part of the core, not an optional performance
  // policy. A core-only session must still be able to bound dead historical
  // state when the configured relief threshold is reached.
  bool rotateEncodingEpochForRelief() const { return true; }
};

} // namespace stp

#endif
