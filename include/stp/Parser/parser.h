/********************************************************************
 * AUTHORS: Vijay Ganesh, Felix Kutzner
 *
 * BEGIN DATE: November, 2005
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

#ifndef PARSER_H
#define PARSER_H

#include "stp/AST/AST.h"
#include "stp/STPManager/STP.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Util/Attributes.h"
#include <cstdio>
#include <string>

namespace stp
{
// external parser table for declared symbols.

// Symbols in generated  files used by tools/stp
void SMTScanString(const char* yy_str);
void SMT2ScanString(const char* yy_str);
void CVCScanString(const char* yy_str);
DLL_PUBLIC FILE* getCVCIn();
DLL_PUBLIC FILE* getSMTIn();
DLL_PUBLIC FILE* getSMT2In();
DLL_PUBLIC void setCVCIn(FILE* file);
DLL_PUBLIC void setSMTIn(FILE* file);
DLL_PUBLIC void setSMT2In(FILE* file);

// Whether the SMT-LIB2 lexer reads a character at a time. Needed when stp
// is driven interactively over a pipe, where block reads would deadlock.
DLL_PUBLIC void setSMT2Interactive(bool enable);

// Whether the SMT-LIB2 lexer recognises the floating-point keywords.
// SMT-LIB reserves theory names per-logic, so they are live only under an
// FP set-logic; outside one, names like "fp", "NaN" or "RNE" stay ordinary
// symbols (QF_BV inputs legitimately declare such names). SMT2Parse()
// starts each script with them off; the set-logic action flips them.
void SMT2SetFloatTokens(bool enable);

// The same question, for the one place that cannot be answered by the lexer
// rules: define-sort's body is swallowed whole and re-tokenised by hand in
// the grammar, so it has to consult the gate itself.
bool SMT2FloatTokensActive();

// The next ordinary identifier is the declaration site of a define-fun
// formal.  The lexer must return its spelling rather than resolving it in a
// top-level namespace; once installed, that temporary binding takes
// precedence while the function body is parsed.
void SMT2ExpectFunctionParameterName();

// Clear command-local lexer expectations after parser recovery/abort and
// before the next top-level command. This includes declaration-name and
// define-fun-formal latches and the declassified-name record below, none of
// which may leak across commands.
void SMT2ResetCommandLexerState();

// The declassified declare-fun name. With uninterpreted functions enabled,
// a name in exactly the declare-fun name position that the lexer WOULD
// classify into a typed token (TERMID_TOK, a *_FUNCTIONID_TOK, a
// UF_*_FUNCTIONID_TOK -- none of which any var_decl alternative accepts) is
// handed back as a plain STRING_TOK instead, and the classification it would
// have received is recorded here: token kind, line, and the token text
// exactly as yyerror would have printed it. That lets the grammar see the
// declaration's SHAPE: only a nonzero-arity declaration continues into the
// nonfatal UF declaration funnel (which consumes the record); every zero-arity
// shape replicates the pinned classified-token syntax error byte-for-byte
// from the record and abandons the parse, exactly as the legacy grammar did
// at the name. Unknown names, and every other position, are untouched.
bool SMT2DeclassifiedNamePending();
int SMT2DeclassifiedNameToken();
int SMT2DeclassifiedNameLine();
const std::string& SMT2DeclassifiedNameText();
void SMT2ConsumeDeclassifiedName();

// Thrown when the parse fails downstream of a declassified declare-fun name
// somewhere bison cannot unwind by itself -- a fatal sort rule, an illegal
// character in the lexer. The pinned response is the name-position error
// ALONE, so the failure in progress must not add its own message or its own
// exit path. Caught in SMT2Parse(), which answers 1 exactly as an ordinary
// abandoned parse does. (A bison syntax error downstream of the name needs
// no throw: yyerror prints the name-position error and returns, and bison's
// own abort reclaims its stack.)
struct DeclassifiedNameAbandon
{
};

// Whether `text` is a floating-point name that the gate above handed to the
// grammar as an ordinary undeclared identifier. The grammar cannot tell that
// apart from a genuine typo, so its diagnostics ask this and append a hint
// naming the set-logic that would have made the name a keyword.
bool SMT2FpKeywordNeedsLogic(const char* text);

DLL_PUBLIC int SMTParse(void* AssertsQuery);
DLL_PUBLIC int SMT2Parse();
DLL_PUBLIC int CVCParse(void* AssertsQuery);
} // end of namespace

DLL_PUBLIC int cvclex_destroy(void);
DLL_PUBLIC int smtlex_destroy(void);
DLL_PUBLIC int smt2lex_destroy(void);

#endif
