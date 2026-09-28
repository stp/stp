#ifndef STP_LRA_AST_REAL_CONST_ACCESS_H
#define STP_LRA_AST_REAL_CONST_ACCESS_H

#include <string>

namespace stp {
class ASTInternal;

namespace lra::detail {

// Private implementation seam used by the public ASTNode string accessors.
// The signature exposes neither ExactRational nor an IMath representation.
std::string realCanonical(const ASTInternal* node);
std::string realNumerator(const ASTInternal* node);
std::string realDenominator(const ASTInternal* node);

} // namespace lra::detail
} // namespace stp

#endif
