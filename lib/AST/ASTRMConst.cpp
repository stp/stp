/********************************************************************
 * A source-language RoundingMode literal over STP's 5-bit carrier.
 ********************************************************************/
#include "stp/AST/ASTRMConst.h"
#include "stp/AST/AST.h"

namespace stp
{

ASTRMConst::ASTRMConst(STPMgr* mgr, CBV bv)
    : ASTBVConst(mgr, bv, 0, /*managed_outside=*/true)
{
}

ASTRMConst::ASTRMConst(const ASTRMConst& other) : ASTBVConst(other) {}

} // namespace stp
