#ifndef STP_LRA_BUDGET_REFUSAL_H
#define STP_LRA_BUDGET_REFUSAL_H

#include <exception>

namespace stp::lra
{

/* Building the LRA problem does exact arithmetic at four layers -- the number
 * budget, the frontend's normalisation, the atom registry, and the solve
 * context that hands the core its rows -- and each refuses in its own
 * currency.  Every one of them spells "a budget said no" the same way: a
 * ResourceLimit kind on an otherwise ordinary exception.  Which class it is
 * records which layer noticed, which matters for a diagnostic and not at all
 * for what the caller should do.
 *
 * One definition, because it was previously written twice and the two copies
 * disagreed: STP.cpp knew all four, c_interface.cpp knew two, so a
 * RegistryFailure or SolveContextFailure carrying ResourceLimit was a budget
 * refusal at the top of the solver and a fatal error one layer down -- the
 * same condition on either side of an internal boundary deciding whether an
 * embedder got a status or lost its process.  Adding a fifth failure class
 * now updates every caller at once.
 *
 * Declared without the failure headers so that callers outside lib/Lra need
 * no part of its private include path; the four classes are matched in
 * LraBudgetRefusal.cpp, where they are all visible. */
bool gaveUpOnABudget(const std::exception& thrown) noexcept;

}  // namespace stp::lra

#endif
