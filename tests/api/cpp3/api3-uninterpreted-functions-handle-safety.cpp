/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: September, 2026
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

// api3-uninterpreted-functions-handle-safety.cpp -- invalid, inactive, stale,
// foreign and released handles presented where a function or its actuals are
// expected; none of them may crash or end the process.
//
// 2.x's UFDeclHandle was an opaque integer token and an Expr a raw pointer,
// so its cases presented impossible tokens, tokens of destroyed or other
// checkers, and deleted or bogus pointers, several in death tests. 3.x has
// neither: a function is a term, and a term is a value that pins its manager,
// so a released handle is a null term and a manager whose own handles are gone
// lives on in what came from it. What is left to check is that every such
// misuse is a recoverable error with the right code -- NULL_HANDLE for a null
// term, SORT_MISMATCH for a term that is not a function, FOREIGN_MANAGER for a
// term of another manager, ARITY for a missing actual -- and that the manager
// stays usable.
//
// A declaration becomes inactive only through a parser scope, and the API
// leaves none behind: the one case that needs an inactive declaration makes
// it through the engine's UF registry (api3_engine.hpp) and then goes back to
// the public API.

#include "api3_engine.hpp"

#include "stp/UninterpretedFunctions/UFContext.h"
#include "stp/UninterpretedFunctions/UFDecl.h"

#include <cstdint>
#include <initializer_list>
#include <optional>
#include <string>
#include <vector>

using namespace stp::api;

namespace
{

// A function over Bool (width 0) and bit-vector sorts, as the 2.x helper
// declared them.
Term declareFunction(TermManager& tm, const char* name,
                     std::initializer_list<unsigned> domainWidths, unsigned codomainWidth)
{
  std::vector<Sort> domain;
  domain.reserve(domainWidths.size());
  for (const unsigned width : domainWidths)
    domain.push_back(width == 0 ? tm.mk_bool_sort() : tm.mk_bv_sort(width));
  const Sort codomain = codomainWidth == 0 ? tm.mk_bool_sort() : tm.mk_bv_sort(codomainWidth);
  return tm.declare(name, tm.mk_fun_sort(domain, codomain));
}

// The options of a 2.x checker: vc_createValidityChecker set 'd', so every
// 2.x case ran with the counterexample self-check on, and every solver here
// runs with check-sanity.
Options checkerOptions()
{
  Options o;
  o.set_bool("check-sanity", true);
  return o;
}

} // namespace

TEST(UninterpretedFunctionsHandleSafety, InvalidAndInactiveDeclarationHandlesAreNonfatal)
{
  TermManager tm;
  const Term declaration = declareFunction(tm, "f", {8}, 8);
  ASSERT_FALSE(declaration.is_null());
  const Term x = tm.declare("x", tm.mk_bv_sort(8));

  // 2.x's impossible token (UINT64_MAX) and an Expr pointer passed as a
  // token: in 3.x, a null term and a term that is not a function.
  API3_EXPECT_ERROR(ErrorCode::NULL_HANDLE, apply({Term(), x}));
  API3_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, x(x));

  // Deactivate the declaration underneath the API, as a parser scope would.
  stp::STPMgr& engine = api3::engine_manager(tm);
  std::string diagnostic;
  const stp::UFDecl* internalDeclaration = engine.getUFContext()->lookup("f");
  ASSERT_NE(nullptr, internalDeclaration);
  ASSERT_TRUE(engine.getUFContext()->deactivate(internalDeclaration, &diagnostic))
      << diagnostic;
  API3_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, declaration(x));

  // Reset/pop-style deactivation frees the engine's name but never recycles
  // the declaration's identity. 3.x: the manager's name table still binds
  // "f" to the deactivated function (only the engine was told), so declare
  // hands the same stale term back; a fresh function of the same shape comes
  // from mk_fresh and works, while the old one stays refused although both
  // have the same shape.
  EXPECT_TRUE(declareFunction(tm, "f", {8}, 8).same_as(declaration));
  const Term replacement = tm.mk_fresh(declaration.sort(), "f");
  ASSERT_FALSE(replacement.is_null());
  EXPECT_FALSE(replacement.same_as(declaration));
  const Term fresh = replacement(x);
  EXPECT_FALSE(fresh.is_null());
  API3_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, declaration(x));
}

TEST(UninterpretedFunctionsHandleSafety,
     DestroyedAndCrossContextDeclarationsAndActualsAreNonfatal)
{
  std::optional<TermManager> owner(std::in_place);
  TermManager other;
  const Term fromOwner = declareFunction(*owner, "owner_f", {8}, 8);
  const Term fromOther = declareFunction(other, "other_f", {8}, 8);
  ASSERT_FALSE(fromOwner.is_null());
  ASSERT_FALSE(fromOther.is_null());

  std::optional<Term> ownerX(owner->declare("owner_x", owner->mk_bv_sort(8)));
  const Term otherX = other.declare("other_x", other.mk_bv_sort(8));

  // Isolate declaration ownership from actual ownership: each call has only
  // one input foreign to the other. (3.x has no checker argument: the
  // actuals must belong to the function's manager.)
  const auto foreignDeclaration = API3_ERROR_OF(fromOwner(otherX));
  ASSERT_TRUE(foreignDeclaration.has_value());
  EXPECT_EQ(foreignDeclaration->code(), ErrorCode::FOREIGN_MANAGER);
  const auto foreignActual = API3_ERROR_OF(fromOther(*ownerX));
  ASSERT_TRUE(foreignActual.has_value());
  EXPECT_EQ(foreignActual->code(), ErrorCode::FOREIGN_MANAGER);

  // 2.x destroyed the owning checker here. In 3.x releasing every other
  // handle of the owner leaves its function term -- and so its manager --
  // valid, and still foreign to the other manager's actuals; nothing freed is
  // inspected.
  ownerX.reset();
  owner.reset();
  API3_EXPECT_ERROR(ErrorCode::FOREIGN_MANAGER, fromOwner(otherX));
  EXPECT_TRUE(fromOwner.manager().symbol("owner_f").has_value());
  const Term validApplication = fromOther(otherX);
  EXPECT_FALSE(validApplication.is_null());
}

// 2.x passed a null actuals array with a count of one, and an array holding a
// null actual. 3.x takes the actuals as terms: a missing actual is an arity
// error, a null one NULL_HANDLE.
TEST(UninterpretedFunctionsHandleSafety, NullActualStorageIsNonfatal)
{
  TermManager tm;
  const Term declaration = declareFunction(tm, "f", {8}, 8);
  ASSERT_FALSE(declaration.is_null());

  API3_EXPECT_ERROR(ErrorCode::ARITY, declaration(std::vector<Term>{}));
  API3_EXPECT_ERROR(ErrorCode::NULL_HANDLE, declaration(Term()));
}

// 2.x passed a bogus pointer as an actual, in a death test. A 3.x term cannot
// be forged: the nearest thing is a term that never referred to anything, the
// null term, and it is refused like any other -- no death test needed.
TEST(UninterpretedFunctionsHandleSafety, InvalidActualPointerDoesNotCrash)
{
  TermManager tm;
  const Term declaration = declareFunction(tm, "f", {8}, 8);
  const Term invalid;

  API3_EXPECT_ERROR(ErrorCode::NULL_HANDLE, declaration(invalid));
  EXPECT_FALSE(declaration(tm.declare("x", tm.mk_bv_sort(8))).is_null());
}

// 2.x deleted an actual and then passed it, in a death test. A released 3.x
// handle is the null term, refused; the term itself lives on in every other
// handle to it.
TEST(UninterpretedFunctionsHandleSafety, DestroyedActualPointerDoesNotCrash)
{
  TermManager tm;
  const Term declaration = declareFunction(tm, "f", {8}, 8);
  Term destroyed = tm.declare("x", tm.mk_bv_sort(8));
  const Term copy = destroyed;
  destroyed = Term();

  API3_EXPECT_ERROR(ErrorCode::NULL_HANDLE, declaration(destroyed));
  EXPECT_FALSE(declaration(copy).is_null());
}

// An actual whose checker was destroyed, in a death test. In 3.x the actual
// keeps its manager alive, and it is refused as foreign to the target's
// function.
TEST(UninterpretedFunctionsHandleSafety, ActualFromDestroyedContextDoesNotCrash)
{
  std::optional<TermManager> owner(std::in_place);
  TermManager target;
  const Term destroyedOwnerActual = owner->declare("x", owner->mk_bv_sort(8));
  const Term declaration = declareFunction(target, "f", {8}, 8);
  owner.reset();

  API3_EXPECT_ERROR(ErrorCode::FOREIGN_MANAGER, declaration(destroyedOwnerActual));
  EXPECT_EQ(destroyedOwnerActual.sort().bv_size(), 8u); // still a live term
}

// The value of an application whose handle was released, in a death test in
// 2.x. With no check behind it the solver has no model (NO_MODEL); a model
// refuses the null term (NULL_HANDLE).
TEST(UninterpretedFunctionsHandleSafety, DestroyedApplicationValueHandleDoesNotCrash)
{
  TermManager tm;
  Solver s(tm, checkerOptions());
  const Term declaration = declareFunction(tm, "f", {8}, 8);
  const Term x = tm.declare("x", tm.mk_bv_sort(8));
  Term application = declaration(x);
  application = Term();

  API3_EXPECT_ERROR(ErrorCode::NO_MODEL, s.value(application));
  s.add(declaration(x) == 1);
  ASSERT_TRUE(s.check_sat().is_sat());
  API3_EXPECT_ERROR(ErrorCode::NULL_HANDLE, s.model().value(application));
  // the application rebuilt from its parts is the same term, and it reads
  EXPECT_EQ(s.model().uint64_value(declaration(x)), 1u);
}

// 2.x released deleted Expr wrappers at once rather than keeping them as
// process-lifetime tombstones, and churned the live registry to catch leaks
// in that ownership path. 3.x terms follow one ownership rule (2.x's
// EXPRDELETE switch has no equivalent): the same churn of applications made
// and released leaves the manager usable.
TEST(UninterpretedFunctionsHandleSafety, DeletedExpressionChurnLeavesTheContextUsable)
{
  TermManager tm;
  Solver s(tm, checkerOptions());
  const Term declaration = declareFunction(tm, "f", {8}, 8);
  ASSERT_FALSE(declaration.is_null());

  for (unsigned attempt = 0; attempt < 100000; ++attempt)
  {
    const Term argument = tm.mk_bv(8, attempt & 0xffu);
    const Term application = declaration(argument);
    ASSERT_FALSE(application.is_null());
  }

  const Term argument = tm.mk_bv(8, 7);
  const Term application = declaration(argument);
  EXPECT_FALSE(application.is_null());
  s.add(application == 3);
  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_EQ(s.model().uint64_value(application), 3u);
}

// 2.x's declaration tokens were monotonic identities, so a stale token could
// not become valid again through a later checker's allocation. In 3.x the
// stale function pins its manager: it stays the function it was, of the
// manager it was, and the 128 managers made after it neither alias it nor
// accept it.
TEST(UninterpretedFunctionsHandleSafety, DestroyedDeclarationCannotBecomeValidThroughAddressReuse)
{
  std::optional<TermManager> original(std::in_place);
  const Term stale = declareFunction(*original, "old_f", {8}, 8);
  ASSERT_FALSE(stale.is_null());
  const std::uint64_t staleManager = stale.manager().id();
  original.reset();

  for (unsigned attempt = 0; attempt < 128; ++attempt)
  {
    TermManager live;
    const Term replacement = declareFunction(live, "replacement_f", {8}, 8);
    ASSERT_FALSE(replacement.is_null());
    EXPECT_FALSE(replacement.same_as(stale));
    EXPECT_NE(live.id(), staleManager);
    const Term x = live.declare("x", live.mk_bv_sort(8));
    API3_EXPECT_ERROR(ErrorCode::FOREIGN_MANAGER, stale(x));
  }
}

TEST(UninterpretedFunctionsHandleSafety, NamespaceRejectionDoesNotDisplaceExistingBinding)
{
  TermManager tm;
  const Term declaration = declareFunction(tm, "f", {8}, 8);
  ASSERT_FALSE(declaration.is_null());
  // 3.x: the same name and sort give the same function (2.x refused the
  // redeclaration); the name at another sort is refused.
  EXPECT_TRUE(declareFunction(tm, "f", {8}, 8).same_as(declaration));
  API3_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, tm.declare("f", tm.mk_bv_sort(8)));

  const Term x = tm.declare("x", tm.mk_bv_sort(8));
  const Term application = declaration(x);
  EXPECT_FALSE(application.is_null());

  API3_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, declareFunction(tm, "x", {8}, 8));
  const Term xAgain = tm.declare("x", tm.mk_bv_sort(8));
  ASSERT_FALSE(xAgain.is_null());
  EXPECT_EQ(x.id(), xAgain.id());

  // the refused declarations displaced nothing
  EXPECT_TRUE(tm.symbol("f")->same_as(declaration));
  EXPECT_TRUE(tm.symbol("x")->same_as(x));
}

TEST(UninterpretedFunctionsHandleSafety, BooleanApplicationUsesSourceSortEquality)
{
  TermManager tm;
  Solver s(tm, checkerOptions());
  const Term predicate = declareFunction(tm, "predicate", {0}, 0);
  ASSERT_FALSE(predicate.is_null());
  const Term argument = tm.mk_true();
  const Term application = predicate(argument);
  ASSERT_FALSE(application.is_null());
  const Term expected = tm.mk_false();
  const Term equality = application == expected;
  ASSERT_FALSE(equality.is_null());
  s.add(equality);
  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_FALSE(s.model().bool_value(application));
}
