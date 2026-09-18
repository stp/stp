/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: September, 2026
 *
 * The double-width spellings of a multiplication overflow check, rewritten
 * into the overflow predicates so they reach the leading-ones detectors.
 ********************************************************************/

#ifndef MULTIPLYOVERFLOWIDIOM_H_
#define MULTIPLYOVERFLOWIDIOM_H_

#include "stp/AST/AST.h"
#include "stp/NodeFactory/NodeFactory.h"
#include <functional>

namespace stp
{

// Whether a term's top bit is a known zero, from whatever domain the caller
// has; empty when it has none.
using TopBitKnownZero = std::function<bool(const ASTNode&)>;

// lhs = rhs is one of the double-width spellings of a multiplication
// overflow check (see the source). Sets out to the predicate form.
bool multiplyOverflowIdiom(NodeFactory* nf, const ASTNode& lhs,
                           const ASTNode& rhs, ASTNode& out,
                           const TopBitKnownZero& topBitKnownZero = nullptr);

} // namespace stp

#endif
