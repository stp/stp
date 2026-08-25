/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: August, 2026
 *
Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
********************************************************************/

#include "stp/UninterpretedFunctions/UFContext.h"
#include "stp/Globals/Globals.h"
#include "stp/STPManager/STPManager.h"
#include <algorithm>
#include <cctype>
#include <sstream>

namespace stp
{

namespace
{
bool isRenderableExternalName(const std::string& name)
{
  // UF models quote every external declaration name. SMT-LIB quoted symbols
  // have no escape for either delimiter character and admit only printable
  // characters. Rejecting at declaration keeps every later model operation
  // total and nonfatal.
  for (const unsigned char c : name)
    if (c == '|' || c == '\\' || !std::isprint(c))
      return false;
  return true;
}
} // namespace

UFContext::UFContext(STPMgr* manager) : manager_(manager)
{
  assert(manager_ != NULL);
}

UFContext::~UFContext()
{
  releaseSolveProtection();
  parserCommandApplications_.clear();
  applications_.clear();
  byIdentity_.clear();
  activeByName_.clear();
  owned_.clear();
  declarations_.clear();
}

void UFContext::setError(std::string* error, const std::string& message) const
{
  if (error != NULL)
    *error = message;
}

const UFDecl*
UFContext::declareFunction(const std::string& name,
                           const std::vector<SourceSort>& domain,
                           const SourceSort& codomain, std::string* error)
{
  if (!manager_->UserFlags.enable_uninterpreted_functions)
  {
    setError(error, "uninterpreted functions are disabled");
    return NULL;
  }
  if (name.empty())
  {
    setError(error, "uninterpreted-function name must not be empty");
    return NULL;
  }
  if (!isRenderableExternalName(name))
  {
    setError(error, "uninterpreted-function name is not representable as an "
                    "SMT-LIB2 quoted symbol");
    return NULL;
  }
  if (STPMgr::isReservedSymbolName(name.c_str()))
  {
    setError(error, "an uninterpreted-function name beginning with '@' or "
                    "'.' is reserved for solver use");
    return NULL;
  }
  std::string signatureError;
  if (!UFSignature::validate(domain, codomain, &signatureError))
  {
    setError(error, "uninterpreted functions: declaration of " + name +
                        ": " + signatureError);
    return NULL;
  }
  if (activeByName_.find(name) != activeByName_.end())
  {
    setError(error, "uninterpreted function '" + name +
                    "' is already declared in the active namespace");
    return NULL;
  }

  const uint64_t id = nextDeclarationId_++;
  std::ostringstream identityName;
  identityName << "@uf_decl_" << id;
  const ASTNode identity =
      manager_->CreateSourceSymbol(identityName.str().c_str(), codomain);
  manager_->noteIntroducedSymbol(identity);

  std::unique_ptr<UFDecl> record(new UFDecl(
      manager_, id, name, UFSignature(domain, codomain), identity));
  const UFDecl* result = record.get();
  declarations_.push_back(std::move(record));
  activeByName_.insert(std::make_pair(name, result));
  byIdentity_.insert(std::make_pair(identity, result));
  owned_.insert(result);
  return result;
}

bool UFContext::deactivate(const UFDecl* decl, std::string* error)
{
  if (!owns(decl))
  {
    setError(error, "uninterpreted-function declaration belongs to another "
                    "context or is invalid");
    return false;
  }
  const std::map<std::string, const UFDecl*>::iterator found =
      activeByName_.find(decl->name());
  if (found == activeByName_.end() || found->second != decl)
  {
    setError(error, "uninterpreted-function declaration is no longer active");
    return false;
  }
  activeByName_.erase(found);
  return true;
}

const UFDecl* UFContext::lookup(const std::string& name) const
{
  const std::map<std::string, const UFDecl*>::const_iterator found =
      activeByName_.find(name);
  return found == activeByName_.end() ? NULL : found->second;
}

void UFContext::collectIdentitySymbols(ASTNodeSet& out) const
{
  for (const std::pair<const ASTNode, const UFDecl*>& entry : byIdentity_)
    out.insert(entry.first);
}

const UFDecl* UFContext::lookupIdentity(const ASTNode& identity) const
{
  if (identity.IsNull() || !identity.IsOwnedBy(manager_))
    return NULL;
  const std::map<ASTNode, const UFDecl*>::const_iterator found =
      byIdentity_.find(identity);
  return found == byIdentity_.end() ? NULL : found->second;
}

bool UFContext::owns(const UFDecl* decl) const
{
  return decl != NULL && owned_.find(decl) != owned_.end();
}

bool UFContext::isActive(const UFDecl* decl) const
{
  if (!owns(decl))
    return false;
  const std::map<std::string, const UFDecl*>::const_iterator found =
      activeByName_.find(decl->name());
  return found != activeByName_.end() && found->second == decl;
}

std::vector<const UFDecl*> UFContext::activeDeclarations() const
{
  std::vector<const UFDecl*> result;
  result.reserve(activeByName_.size());
  for (const std::pair<const std::string, const UFDecl*>& entry :
       activeByName_)
    result.push_back(entry.second);
  std::sort(result.begin(), result.end(),
            [](const UFDecl* left, const UFDecl* right)
            { return left->id() < right->id(); });
  return result;
}

bool UFContext::validateApplicationChildren(ASTChildren children,
                                            std::string* error) const
{
  if (children.empty())
  {
    setError(error, "UF_APPLY requires a declaration identity");
    return false;
  }
  if (!children[0].IsOwnedBy(manager_))
  {
    setError(error, "UF_APPLY declaration identity belongs to another context");
    return false;
  }
  const UFDecl* decl = lookupIdentity(children[0]);
  if (decl == NULL)
  {
    setError(error, "UF_APPLY child 0 is not a registered declaration identity");
    return false;
  }
  if (children.size() - 1 != decl->signature().arity())
  {
    const size_t expected = decl->signature().arity();
    const size_t actual = children.size() - 1;
    setError(error, "uninterpreted functions: " + decl->name() + " expects " +
                        std::to_string(expected) +
                        (expected == 1 ? " argument" : " arguments") +
                        " but was applied to " + std::to_string(actual));
    return false;
  }
  for (size_t i = 1; i < children.size(); ++i)
  {
    if (!children[i].IsOwnedBy(manager_))
    {
      setError(error, "uninterpreted functions: argument " +
                          std::to_string(i - 1) + " of " + decl->name() +
                          " belongs to another context");
      return false;
    }
    const SourceSort& expected = decl->signature().domain()[i - 1];
    const SourceSort actual = children[i].GetSourceSort();
    if (actual != expected)
    {
      setError(error, "uninterpreted functions: argument " +
                          std::to_string(i - 1) + " of " + decl->name() +
                          " has sort " + sourceSortToSMTLib(actual) +
                          " but the declaration requires " +
                          sourceSortToSMTLib(expected));
      return false;
    }
  }
  return true;
}

ASTNode UFContext::apply(const UFDecl* decl, const ASTVec& actuals,
                         std::string* error)
{
  if (!manager_->UserFlags.enable_uninterpreted_functions)
  {
    setError(error, "uninterpreted functions are disabled");
    return manager_->ASTUndefined;
  }
  if (!owns(decl))
  {
    setError(error, "uninterpreted-function declaration belongs to another "
                    "context or is invalid");
    return manager_->ASTUndefined;
  }
  if (!isActive(decl))
  {
    setError(error, "uninterpreted-function declaration is no longer active");
    return manager_->ASTUndefined;
  }

  ASTVec children;
  children.reserve(actuals.size() + 1);
  children.push_back(decl->identityNode());
  children.insert(children.end(), actuals.begin(), actuals.end());
  if (!validateApplicationChildren(children, error))
    return manager_->ASTUndefined;

  const SourceSort& resultSort = decl->signature().codomain();
  ASTNode result;
  if (resultSort.kind() == SourceSort::Kind::Bool)
    result = manager_->defaultNodeFactory->CreateNode(UF_APPLY, children);
  else
    result = manager_->defaultNodeFactory->CreateTerm(
        UF_APPLY, resultSort.packedWidth(), children);
  noteApplication(result);
  return result;
}

void UFContext::beginParserCommand()
{
  // A parser cannot start the next top-level command until the preceding
  // command's closing parenthesis has committed or rolled it back.
  assert(!parserCommandActive_);
  parserCommandApplications_.clear();
  parserCommandActive_ = true;
}

void UFContext::finishParserCommand(const bool accepted)
{
  // The UF context may have been created during a command (most commonly by
  // its first declaration), after Cpp_interface had a context to begin. Such
  // a command has no application prefix to transact.
  if (!parserCommandActive_)
    return;
  if (!accepted)
    for (const ASTNode& application : parserCommandApplications_)
      applications_.erase(application);
  parserCommandApplications_.clear();
  parserCommandActive_ = false;
}

void UFContext::noteApplication(const ASTNode& application)
{
  assert(application.GetKind() == UF_APPLY);
  const bool inserted = applications_.insert(application).second;
  if (inserted && parserCommandActive_)
    parserCommandApplications_.push_back(application);
}

bool UFContext::isRegisteredApplication(const ASTNode& application) const
{
  return !application.IsNull() && application.IsOwnedBy(manager_) &&
         application.GetKind() == UF_APPLY &&
         applications_.find(application) != applications_.end();
}

bool UFContext::isActiveApplication(const ASTNode& application) const
{
  return isRegisteredApplication(application) && application.Degree() >= 1 &&
         isActive(lookupIdentity(application[0]));
}

void UFContext::beginSolveProtection()
{
  assert(!solveProtectionActive_);
  protectedSymbols_.clear();
  solveScalars_.clear();
}

void UFContext::installSolveProtection(
    const ASTNodeSet& protectedSymbols, const ASTNodeSet& solveScalars)
{
  assert(!solveProtectionActive_);
  for (const ASTNode& scalar : solveScalars)
  {
    if (scalar.IsNull() || !scalar.IsOwnedBy(manager_) ||
        scalar.GetKind() != SYMBOL ||
        protectedSymbols.find(scalar) == protectedSymbols.end())
      FatalError("UF solve scalar is malformed or is not preprocessing "
                 "protected",
                 scalar);
  }
  protectedSymbols_ = protectedSymbols;
  solveScalars_ = solveScalars;
}

void UFContext::releaseSolveProtection()
{
  protectedSymbols_.clear();
  solveScalars_.clear();
  solveProtectionActive_ = false;
}

bool UFContext::isProtected(const ASTNode& symbol) const
{
  return !symbol.IsNull() && symbol.IsOwnedBy(manager_) &&
         symbol.GetKind() == SYMBOL &&
         protectedSymbols_.find(symbol) != protectedSymbols_.end();
}

bool UFContext::isSolveScalar(const ASTNode& symbol) const
{
  return !symbol.IsNull() && symbol.IsOwnedBy(manager_) &&
         symbol.GetKind() == SYMBOL &&
         solveScalars_.find(symbol) != solveScalars_.end();
}

UFContext::SolveScope::SolveScope(UFContext* context) : context_(context)
{
  if (context_ == NULL)
    return;
  assert(!context_->solveProtectionActive_);
  context_->solveProtectionActive_ = true;
}

UFContext::SolveScope::~SolveScope()
{
  if (context_ != NULL)
    context_->solveProtectionActive_ = false;
}

} // namespace stp
