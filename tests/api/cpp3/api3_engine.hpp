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

// api3_engine.hpp -- test-only access to the engine behind the 3.x objects,
// for the suites that check an internal property rather than an answer: that
// an option reaches the engine's flag, what the extensionality checker holds,
// whether the incremental driver engaged. Everything else in such a suite goes
// through the public API.
//
// Including lib/Api/Internal.h defines STP_API_INTERNAL, under which stp.hpp
// does not bring the API's names into namespace stp (the engine has its own
// stp::Kind). A suite that includes this header therefore writes
// `using namespace stp::api;` and names engine types in full (stp::STPMgr).
// An engine header also puts `using stp::Kind;` at global scope, so there the
// API's kinds are written stp::api::Kind. The target needs
// ${PROJECT_SOURCE_DIR}/lib on its include path.

#ifndef STP_TESTS_API3_ENGINE_HPP
#define STP_TESTS_API3_ENGINE_HPP

// stp.hpp included before this point has already brought the API's names into
// namespace stp, where the engine headers below would collide with them.
#if defined(STP_STP_HPP) && !defined(STP_API_INTERNAL)
#error "include api3_engine.hpp before any other STP header"
#endif

#include "Api/Internal.h"

#include "api3_common.hpp"

namespace api3
{

// The engine manager behind a term manager: one per TermManager, shared by
// every solver over it.
inline stp::STPMgr& engine_manager(const stp::api::TermManager& tm)
{
  return *tm.impl()->bm;
}

// The engine solver behind a solver.
inline stp::STP& engine_solver(const stp::api::Solver& s)
{
  return *s.impl()->stp;
}

// The engine's flags as `s` has them. The engine keeps one set of flags per
// manager and holds the active solver's options in it, so this makes `s` the
// active solver and applies its options, as its next check would.
inline stp::UserDefinedFlags& engine_flags(stp::api::Solver& s)
{
  stp::api::detail::SolverImpl* impl = s.impl();
  impl->enter("api3::engine_flags");
  impl->apply_options("api3::engine_flags");
  return impl->mgr->bm->UserFlags;
}

// The engine node behind a term, and a term for an engine node built on the
// manager's own STPMgr (a node the public constructors do not make).
inline stp::ASTNode engine_node(const stp::api::Term& t)
{
  return stp::api::detail::node_of(t);
}
inline stp::api::Term api_term(const stp::api::TermManager& tm,
                               const stp::ASTNode& n)
{
  return stp::api::detail::make_term(tm.impl(), n);
}

} // namespace api3

#endif
