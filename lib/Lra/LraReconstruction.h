#ifndef STP_LRA_RECONSTRUCTION_H
#define STP_LRA_RECONSTRUCTION_H
#include "RealModel.h"

namespace stp::lra
{
struct LraReconstruction
{
  /* The query as the caller wrote it, before presolve rewrote anything.
   * Always recorded, because the model commit checks its model against this
   * as well as against the formula it actually solved. */
  ASTNode original;
};
} // namespace stp::lra
#endif
