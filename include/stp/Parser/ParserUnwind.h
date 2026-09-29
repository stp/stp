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

#ifndef STP_PARSER_PARSERUNWIND_H
#define STP_PARSER_PARSERUNWIND_H

#include <cstdlib>
#include <exception>
#include <tuple>
#include <utility>

namespace stp
{

// Runs `reclaim` when the scope holding it is left by an exception, and
// does nothing when the scope is left normally.
template <class Reclaim> class ParserUnwindGuard
{
public:
  explicit ParserUnwindGuard(Reclaim reclaim)
      : reclaim_(std::move(reclaim)), uncaught_(std::uncaught_exceptions())
  {
  }
  ParserUnwindGuard(const ParserUnwindGuard&) = delete;
  ParserUnwindGuard& operator=(const ParserUnwindGuard&) = delete;
  ~ParserUnwindGuard()
  {
    if (std::uncaught_exceptions() > uncaught_)
      reclaim_();
  }

private:
  Reclaim reclaim_;
  const int uncaught_;
};

// Calls a generated parser's yydestruct on one semantic value. Its
// symbol-kind parameter is an int before Bison 3.6 and an enumeration from
// then on, and each %parse-param adds a trailing parameter; both are deduced
// from yydestruct itself, so one spelling serves every grammar.
template <class... Params> class ParserValueDiscarder
{
public:
  explicit ParserValueDiscarder(Params... params) : params_(params...) {}

  template <class Kind, class Value, class... Declared>
  void operator()(void (*destruct)(const char*, Kind, Value*, Declared...),
                  int kind, Value* value) const
  {
    std::apply(
        [&](Params... params) {
          destruct("Cleanup: unwinding", static_cast<Kind>(kind), value,
                   params...);
        },
        params_);
  }

private:
  std::tuple<Params...> params_;
};

template <class... Params>
ParserValueDiscarder<Params...> parserValueDiscarder(Params... params)
{
  return ParserValueDiscarder<Params...>(params...);
}

// Releases one semantic value and empties the parser stack slot that held
// it. Every release of a value on the stack goes through here (a grammar
// helper that consumes an operand takes the slot by reference), so a slot is
// either live or null: whatever the stack still holds when a parse is
// abandoned can be reclaimed, whichever action was running.
template <class T> void releaseParserValue(T*& value)
{
  delete value;
  value = nullptr;
}

// The same, for the C strings a lexer made with strdup.
inline void releaseParserString(char*& text)
{
  std::free(text);
  text = nullptr;
}

} // namespace stp

// Bison's C skeleton reclaims its stacks when a parse ends by YYABORT,
// YYACCEPT or an unrecovered syntax error: the lookahead token and every
// semantic value on the stack go through the grammar's %destructor rules. A
// C++ exception unwinding through yyparse() -- a grammar refusal
// (ParseAbandon), an engine refusal (EngineFatal), a script that ends at its
// CNF (ScriptEnded) -- skipped all of it, and in a process that parses again
// every abandoned parse leaked what it had read.
//
// Written as a grammar's %initial-action,
//
//   %initial-action { STP_PARSER_RECLAIM_ON_UNWIND() }
//
// (with the grammar's %parse-param names as the arguments, if it has any)
// this gives such an exception that cleanup. It reclaims the right-hand side
// of the action that threw as well, which bison's own YYABORT leaves to the
// action: the values a throwing action already released are null in their
// slots (releaseParserValue), and the rest are still its operands.
//
// Bison places the initial action in yyparse()'s outermost scope, after the
// stacks are set up and before the first token is read, as a braced block;
// the macro closes that block and opens another, so the guard it declares
// lives for the whole parse, and every name it uses is yyparse()'s own. The
// lookahead is compared with the value yychar holds at that point, which is
// the skeleton's "no lookahead" token under every prefix.
#define STP_PARSER_RECLAIM_ON_UNWIND(...)                                      \
  }                                                                            \
  const int stp_parser_no_lookahead = yychar;                                  \
  const auto stp_parser_discard = stp::parserValueDiscarder(__VA_ARGS__);      \
  auto stp_parser_reclaim = [&]() {                                            \
    if (yychar != stp_parser_no_lookahead)                                     \
      stp_parser_discard(yydestruct, YYTRANSLATE(yychar), &yylval);            \
    while (yyssp != yyss)                                                      \
    {                                                                          \
      stp_parser_discard(yydestruct, yystos[+*yyssp], yyvsp);                  \
      YYPOPSTACK(1);                                                           \
    }                                                                          \
    if (yyss != yyssa)                                                         \
      YYSTACK_FREE(yyss);                                                      \
  };                                                                           \
  const stp::ParserUnwindGuard<decltype(stp_parser_reclaim)>                   \
      stp_parser_unwind_guard(stp_parser_reclaim);                             \
  {

// YYABORT from inside an action, with the action's right-hand side reclaimed
// along with the rest of the stack: bison's YYABORT pops the right-hand side
// unreclaimed, leaving it to the action, and this hands it back. As with the
// guard above, what the action already released is null in its slot.
#define STP_PARSER_ABORT()                                                     \
  do                                                                           \
  {                                                                            \
    yylen = 0;                                                                 \
    YYABORT;                                                                   \
  } while (0)

#endif
