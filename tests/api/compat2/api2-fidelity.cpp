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

// api2-fidelity.cpp -- 2.x behaviours libstp2 once got wrong.
//
// The 2.x suites in this directory run against libstp2 unchanged; the cases
// here pin what they did not reach, each against what 2.x itself did.

#include "stp/c_interface.h"

#include <gtest/gtest.h>

#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <string>
#include <vector>

namespace
{

std::string text_of(Expr e)
{
  char* s = exprString(e);
  std::string out = s != nullptr ? s : "";
  std::free(s);
  return out;
}

// vc_parseMemExpr hands back the ASSERTs and the QUERY apart, asserting only
// the former. The query here is not valid, so neither it nor FALSE may come
// out valid after the parse.
TEST(libstp2_fidelity, a_parsed_query_that_is_not_valid_stays_so)
{
  VC vc = vc_createValidityChecker();
  Expr query = nullptr, asserts = nullptr;
  ASSERT_EQ(1, vc_parseMemExpr(vc, "x : BITVECTOR(8); ASSERT(x = 0hex01); QUERY x = 0hex02;", &query,
                               &asserts));
  EXPECT_NE(std::string::npos, text_of(asserts).find("0x01")) << text_of(asserts);
  EXPECT_EQ(std::string::npos, text_of(asserts).find("FALSE")) << text_of(asserts);
  EXPECT_EQ(0, vc_query(vc, query));
  EXPECT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  vc_DeleteExpr(query);
  vc_DeleteExpr(asserts);
  vc_Destroy(vc);
}

// The parser asserts a query's negation, and drops one that folds to TRUE:
// a query that asserts nothing is FALSE, or folds to it, and parses as FALSE.
TEST(libstp2_fidelity, a_false_query_parses_as_false)
{
  for (const char* text : {"x : BITVECTOR(8); ASSERT(x = 0hex01); QUERY FALSE;",
                           "x : BITVECTOR(8); ASSERT(x = 0hex01); QUERY x /= x;"})
  {
    VC vc = vc_createValidityChecker();
    Expr query = nullptr, asserts = nullptr;
    ASSERT_EQ(1, vc_parseMemExpr(vc, text, &query, &asserts)) << text;
    EXPECT_EQ(FALSE, getExprKind(query)) << text << ": " << text_of(query);
    EXPECT_EQ(0, vc_query(vc, query)) << text;
    vc_DeleteExpr(query);
    vc_DeleteExpr(asserts);
    vc_Destroy(vc);
  }
}

// A ';' in a comment inside the QUERY statement does not end it.
TEST(libstp2_fidelity, a_comment_in_a_query_is_skipped)
{
  VC vc = vc_createValidityChecker();
  Expr query = nullptr, asserts = nullptr;
  ASSERT_EQ(1, vc_parseMemExpr(vc,
                               "x : BITVECTOR(8); ASSERT(x = 0hex01); "
                               "QUERY x = % ; a comment\n 0hex02;",
                               &query, &asserts));
  EXPECT_NE(std::string::npos, text_of(query).find("0x02")) << text_of(query);
  EXPECT_EQ(0, vc_query(vc, query));
  vc_DeleteExpr(query);
  vc_DeleteExpr(asserts);
  vc_Destroy(vc);
}

// A name the lexer reads whole is not the QUERY keyword, whatever it contains.
TEST(libstp2_fidelity, a_name_containing_query_is_a_name)
{
  for (const char* name : {"x$QUERY", "x?QUERY", "QUERY'", "_QUERY"})
  {
    const std::string text = std::string(name) + " : BOOLEAN; ASSERT(NOT " + name + "); QUERY " +
                             name + ";";
    VC vc = vc_createValidityChecker();
    Expr query = nullptr, asserts = nullptr;
    ASSERT_EQ(1, vc_parseMemExpr(vc, text.c_str(), &query, &asserts)) << text;
    EXPECT_NE(std::string::npos, text_of(query).find(name)) << text_of(query);
    EXPECT_EQ(0, vc_query(vc, query)) << text;
    vc_DeleteExpr(query);
    vc_DeleteExpr(asserts);
    vc_Destroy(vc);
  }
}

// vc_paramBoolExpr names its variable after the application as 2.x printed
// it, so a one-bit and a four-bit parameter of one value name two variables.
TEST(libstp2_fidelity, parameters_of_two_widths_name_two_variables)
{
  VC vc = vc_createValidityChecker();
  Expr p = vc_varExpr1(vc, "p", 0, 0);
  Expr one_bit = vc_paramBoolExpr(vc, p, vc_bvConstExprFromInt(vc, 1, 1));
  Expr four_bit = vc_paramBoolExpr(vc, p, vc_bvConstExprFromInt(vc, 4, 1));
  EXPECT_EQ("p (0b1 ) ", text_of(one_bit));
  EXPECT_EQ("p (0x1 ) ", text_of(four_bit));
  EXPECT_EQ(0, vc_query(vc, vc_iffExpr(vc, one_bit, four_bit)));
  // the same parameter names the same variable
  Expr again = vc_paramBoolExpr(vc, p, vc_bvConstExprFromInt(vc, 1, 1));
  EXPECT_EQ(1, vc_query(vc, vc_iffExpr(vc, one_bit, again)));
  vc_Destroy(vc);
}

std::string g_fatal;

// A whole counterexample answers for a symbol and for a cell of an array
// symbol the model has, as 2.x's map did, and hands any other term back as
// it is: a term built after the check is not evaluated against it.
TEST(libstp2_fidelity, a_whole_counterexample_hands_back_what_it_does_not_record)
{
  VC vc = vc_createValidityChecker();
  Expr x = vc_varExpr1(vc, "x", 0, 8);
  Expr y = vc_varExpr1(vc, "y", 0, 8);
  Expr a = vc_varExpr1(vc, "a", 8, 8);
  vc_assertFormula(vc, vc_eqExpr(vc, x, vc_bvConstExprFromInt(vc, 8, 7)));
  vc_assertFormula(vc, vc_eqExpr(vc, vc_readExpr(vc, a, vc_bvConstExprFromInt(vc, 8, 3)),
                                 vc_bvConstExprFromInt(vc, 8, 9)));
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  WholeCounterExample m = vc_getWholeCounterExample(vc);
  Expr x_value = vc_getTermFromCounterExample(vc, x, m);
  Expr y_value = vc_getTermFromCounterExample(vc, y, m); // left out: zero
  Expr cell = vc_getTermFromCounterExample(vc, vc_readExpr(vc, a, vc_bvConstExprFromInt(vc, 8, 3)), m);
  Expr no_cell = vc_getTermFromCounterExample(vc, vc_readExpr(vc, a, vc_bvConstExprFromInt(vc, 8, 4)), m);
  Expr sum = vc_getTermFromCounterExample(vc, vc_bvPlusExpr(vc, 8, x, vc_bvConstExprFromInt(vc, 8, 1)), m);
  EXPECT_EQ(7, getBVInt(x_value));
  EXPECT_EQ(0, getBVInt(y_value));
  EXPECT_EQ(9, getBVInt(cell));
  EXPECT_EQ(READ, getExprKind(no_cell));
  EXPECT_EQ(BVPLUS, getExprKind(sum));
  // a Boolean that is not a variable is refused, as 2.x refused it
  vc_registerErrorHandler([](const char* msg) { g_fatal = msg; });
  vc_setErrorPolicy(STP_ON_ERROR_RETURN);
  EXPECT_EQ(nullptr, vc_getTermFromCounterExample(vc, vc_eqExpr(vc, x, y), m));
  vc_setErrorPolicy(STP_ON_ERROR_ABORT);
  vc_registerErrorHandler(nullptr);
  EXPECT_NE(std::string::npos, g_fatal.find("propositional variables")) << g_fatal;
  for (Expr e : {x_value, y_value, cell, no_cell, sum})
    vc_DeleteExpr(e);
  vc_deleteWholeCounterExample(m);
  vc_Destroy(vc);
}

// A whole counterexample also answers for what vc_getCounterExample
// evaluated before it was taken, as 2.x's map had kept it: the term and the
// terms the evaluation visited on the way -- of an if-then-else only the
// branch the model selects -- but not a term read after the snapshot.
TEST(libstp2_fidelity, a_whole_counterexample_holds_what_was_evaluated_before_it)
{
  VC vc = vc_createValidityChecker();
  Expr x = vc_varExpr1(vc, "x", 0, 8);
  Expr seven = vc_bvConstExprFromInt(vc, 8, 7);
  Expr two = vc_bvConstExprFromInt(vc, 8, 2);
  vc_assertFormula(vc, vc_eqExpr(vc, x, seven));
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  Expr sum = vc_bvPlusExpr(vc, 8, x, two);
  Expr product = vc_bvMultExpr(vc, 8, sum, two);
  Expr untaken = vc_bvPlusExpr(vc, 8, x, vc_bvConstExprFromInt(vc, 8, 5));
  Expr choice = vc_iteExpr(vc, vc_eqExpr(vc, x, seven), product, untaken);
  Expr later = vc_bvPlusExpr(vc, 8, x, vc_bvConstExprFromInt(vc, 8, 3));
  vc_DeleteExpr(vc_getCounterExample(vc, choice));
  WholeCounterExample m = vc_getWholeCounterExample(vc);
  vc_DeleteExpr(vc_getCounterExample(vc, later));
  std::vector<Expr> read;
  for (Expr e : {choice, product, sum, untaken, later})
    read.push_back(vc_getTermFromCounterExample(vc, e, m));
  EXPECT_EQ(18, getBVInt(read[0]));
  EXPECT_EQ(18, getBVInt(read[1]));
  EXPECT_EQ(9, getBVInt(read[2]));
  EXPECT_EQ(BVPLUS, getExprKind(read[3]));
  EXPECT_EQ(BVPLUS, getExprKind(read[4]));
  for (Expr e : read)
    vc_DeleteExpr(e);
  vc_deleteWholeCounterExample(m);
  vc_Destroy(vc);
}

// A read went its own way in 2.x's evaluation: past the last write it read
// the base at the index's value, and kept that read; over an if-then-else it
// read the branch the model selects, and kept that read but not the read
// over the if-then-else. A snapshot answers for exactly those.
TEST(libstp2_fidelity, a_whole_counterexample_holds_the_reads_an_evaluation_made)
{
  VC vc = vc_createValidityChecker();
  Expr a = vc_varExpr1(vc, "a", 8, 8), b = vc_varExpr1(vc, "b", 8, 8);
  Expr i = vc_varExpr1(vc, "i", 0, 8), p = vc_varExpr1(vc, "p", 0, 0);
  Expr one = vc_bvConstExprFromInt(vc, 8, 1), two = vc_bvConstExprFromInt(vc, 8, 2);
  vc_assertFormula(vc, vc_eqExpr(vc, i, two));
  vc_assertFormula(vc, p);
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  Expr past_the_write = vc_readExpr(vc, vc_writeExpr(vc, a, one, vc_bvConstExprFromInt(vc, 8, 7)), i);
  Expr over_the_ite = vc_readExpr(vc, vc_iteExpr(vc, p, a, b), i);
  vc_DeleteExpr(vc_getCounterExample(vc, past_the_write));
  vc_DeleteExpr(vc_getCounterExample(vc, over_the_ite));
  WholeCounterExample m = vc_getWholeCounterExample(vc);
  std::vector<Expr> read;
  for (Expr e : {past_the_write, vc_readExpr(vc, a, two), over_the_ite})
    read.push_back(vc_getTermFromCounterExample(vc, e, m));
  EXPECT_EQ(BVCONST, getExprKind(read[0]));
  EXPECT_EQ(BVCONST, getExprKind(read[1])) << text_of(read[1]); // the base read built
  EXPECT_EQ(READ, getExprKind(read[2])) << text_of(read[2]);    // not kept
  for (Expr e : read)
    vc_DeleteExpr(e);
  vc_deleteWholeCounterExample(m);
  vc_Destroy(vc);
}

// A Real term's counterexample value is the exact Real model's, and an
// assertion, a parsed one included, a declaration, or a parsed CVC query
// since the query leaves that model none.
TEST(libstp2_fidelity, a_stale_real_model_has_no_counterexample_value)
{
  VC vc = vc_createValidityChecker();
  Expr x = vc_varExpr(vc, "x", vc_realType(vc));
  vc_assertFormula(vc, vc_eqExpr(vc, x, vc_realConstExprFromStr(vc, "1")));
  for (int stale = 0; stale < 4; ++stale)
  {
    ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
    Expr v = vc_getCounterExample(vc, x);
    ASSERT_NE(nullptr, v);
    EXPECT_EQ(REAL_CONST, getExprKind(v));
    vc_DeleteExpr(v);
    if (stale == 0)
      vc_assertFormula(vc, vc_trueExpr(vc));
    else if (stale == 1)
      vc_varExpr(vc, "y", vc_realType(vc));
    else if (stale == 2)
      ASSERT_EQ(1, vc_parseMemExpr(vc, "ASSERT(TRUE); QUERY TRUE;", nullptr, nullptr));
    else
      ASSERT_EQ(1, vc_parseMemExpr(vc, "QUERY TRUE;", nullptr, nullptr));
    EXPECT_EQ(0, vc_hasRealModel(vc)) << stale;
    EXPECT_EQ(0, vc_hasRealModelValue(vc, x)) << stale;
    EXPECT_EQ(nullptr, vc_getCounterExample(vc, x)) << stale;
  }
  vc_Destroy(vc);
}

} // namespace

// A CVC text that asserts anything hands back, as its assertions, the
// conjunction of every assertion the checker holds -- 2.x's GetAsserts(), with
// the ones made before the text and every level's -- and one that asserts
// nothing hands back TRUE. libstp2 handed back the text's own alone, so with
// FALSE asserted first "ASSERT TRUE; QUERY FALSE;" came back TRUE where 2.x
// gave FALSE, and vc_parseExpr's conjunction lost the FALSE too.
TEST(libstp2_fidelity, a_cvc_text_hands_back_every_assertion)
{
  VC vc = vc_createValidityChecker();
  vc_assertFormula(vc, vc_falseExpr(vc));
  Expr query = nullptr, asserts = nullptr;
  ASSERT_EQ(1, vc_parseMemExpr(vc, "ASSERT TRUE; QUERY FALSE;", &query, &asserts));
  EXPECT_EQ(FALSE, getExprKind(asserts)) << text_of(asserts);
  vc_DeleteExpr(query);
  vc_DeleteExpr(asserts);
  {
    std::ofstream("api2-fidelity-parse.cvc") << "ASSERT TRUE; QUERY FALSE;\n";
    Expr parsed = vc_parseExpr(vc, "api2-fidelity-parse.cvc");
    ASSERT_NE(nullptr, parsed);
    EXPECT_EQ(FALSE, getExprKind(parsed)) << text_of(parsed);
    vc_DeleteExpr(parsed);
    std::remove("api2-fidelity-parse.cvc");
  }
  vc_Destroy(vc);

  vc = vc_createValidityChecker();
  Expr x = vc_varExpr(vc, "x", vc_bvType(vc, 8));
  vc_assertFormula(vc, vc_eqExpr(vc, x, vc_bvConstExprFromInt(vc, 8, 1)));
  vc_push(vc);
  Expr y = vc_varExpr(vc, "y", vc_bvType(vc, 8));
  vc_assertFormula(vc, vc_eqExpr(vc, y, vc_bvConstExprFromInt(vc, 8, 2)));
  ASSERT_EQ(1, vc_parseMemExpr(vc, "z : BITVECTOR(8); ASSERT(z = 0hex03); QUERY FALSE;", &query,
                               &asserts));
  EXPECT_EQ(AND, getExprKind(asserts)) << text_of(asserts);
  EXPECT_EQ(3, getDegree(asserts)) << text_of(asserts);
  vc_DeleteExpr(query);
  vc_DeleteExpr(asserts);
  // a text that asserts nothing hands back TRUE, whatever the checker holds
  ASSERT_EQ(1, vc_parseMemExpr(vc, "QUERY FALSE;", &query, &asserts));
  EXPECT_EQ(TRUE, getExprKind(asserts)) << text_of(asserts);
  vc_DeleteExpr(query);
  vc_DeleteExpr(asserts);
  vc_Destroy(vc);
}

// KLEE's commonest shape: a constant table of 256 or more entries, flushed as
// a write chain, indexed by one symbolic byte of an input that is read once.
// Unconstrained-variable elimination substitutes the input by a write over a
// fresh array, and the model of every invalid query refused that entry
// fatally, so KLEE's read of the byte met the error handler. 2.x answered it,
// and so does libstp2: input[0] = 0 is the only index whose entry is 0.
// vc_getCounterExampleArray, which died on that entry in 2.x too, now hands
// the input's cell back.
TEST(libstp2_fidelity, a_table_indexed_by_a_symbolic_byte_has_a_counterexample)
{
  for (int n : {256, 300, 1000})
  {
    VC vc = vc_createValidityChecker();
    vc_setInterfaceFlags(vc, EXPRDELETE, 0);
    Type i32 = vc_bvType(vc, 32), i8 = vc_bvType(vc, 8);
    Type at = vc_arrayType(vc, i32, i8);
    Expr input = vc_varExpr(vc, "input", at);
    Expr table = vc_varExpr(vc, "table", at);
    for (int i = 0; i < n; ++i)
      table = vc_writeExpr(vc, table, vc_bvConstExprFromInt(vc, 32, i),
                           vc_bvConstExprFromInt(vc, 8, (i * 7) & 0xff));
    Expr byte = vc_readExpr(vc, input, vc_bvConstExprFromInt(vc, 32, 0));
    Expr lookup =
        vc_readExpr(vc, table, vc_bvConcatExpr(vc, vc_bvConstExprFromLL(vc, 24, 0), byte));
    vc_push(vc);
    vc_assertFormula(vc, vc_eqExpr(vc, lookup, vc_bvConstExprFromInt(vc, 8, 0)));
    EXPECT_EQ(0, vc_query(vc, vc_falseExpr(vc))) << n;
    Expr value = vc_getCounterExample(vc, byte);
    ASSERT_NE(nullptr, value) << n;
    EXPECT_EQ(0u, getBVUnsigned(value)) << n;
    Expr* indices = nullptr;
    Expr* values = nullptr;
    int size = 0;
    vc_getCounterExampleArray(vc, input, &indices, &values, &size);
    bool found = false;
    for (int k = 0; k < size; ++k)
      if (getBVUnsigned(indices[k]) == 0)
      {
        found = true;
        EXPECT_EQ(0u, getBVUnsigned(values[k])) << n;
      }
    EXPECT_TRUE(found) << n;
    vc_deleteCounterExampleArray(indices, values, size);
    vc_pop(vc);
    vc_Destroy(vc);
  }
}

// A CVC text that a grammar action rejects -- an unresolved name, operands of
// two widths -- is a failed parse reported through the handler. The action
// went on building from what it had rejected: the unresolved name crashed
// the process without reaching the handler under either error policy, and
// the width mismatch parsed "successfully" into a formula no one wrote.
// (2.x called the handler and aborted; STP_ON_ERROR_RETURN returns instead.)
namespace
{
int parse_errors = 0;
void count_parse_error(const char*)
{
  ++parse_errors;
}
} // namespace

TEST(libstp2_fidelity, a_rejected_cvc_text_is_a_failed_parse)
{
  vc_registerErrorHandler(count_parse_error);
  vc_setErrorPolicy(STP_ON_ERROR_RETURN);
  for (const char* text : {"x : BITVECTOR(8); ASSERT(y = 0hex01); QUERY(x = x);",
                           "x : BITVECTOR(8); ASSERT((x & 0hex001) = 0hex01); QUERY(FALSE);",
                           "x : BITVECTOR(8); ASSERT((x | 0hex001) = 0hex000); QUERY(FALSE);"})
  {
    VC vc = vc_createValidityChecker();
    Expr query = nullptr, asserts = nullptr;
    parse_errors = 0;
    EXPECT_NE(1, vc_parseMemExpr(vc, text, &query, &asserts)) << text;
    EXPECT_EQ(1, parse_errors) << text;
    // the checker is usable afterwards
    Expr z = vc_varExpr(vc, "z", vc_bvType(vc, 8));
    vc_assertFormula(vc, vc_eqExpr(vc, z, vc_bvConstExprFromInt(vc, 8, 7)));
    EXPECT_EQ(0, vc_query(vc, vc_falseExpr(vc))) << text;
    vc_Destroy(vc);
  }
  vc_setErrorPolicy(STP_ON_ERROR_ABORT);
  vc_registerErrorHandler(nullptr);
}

// 2.x read the counterexample of a term, and simplified one, at any depth its
// solve reached; libstp2 overflowed the C++ stack in the model's evaluator
// from about 40 000 levels and in vc_simplify from 80 000.
TEST(libstp2_fidelity, a_deep_term_is_read_back_and_simplified)
{
  VC vc = vc_createValidityChecker();
  vc_setFlags(vc, 'i', 0);
  Expr chain = vc_varExpr(vc, "x0", vc_boolType(vc));
  for (int i = 1; i < 100000; ++i)
  {
    const std::string name = "x" + std::to_string(i);
    Expr v = vc_varExpr(vc, name.c_str(), vc_boolType(vc));
    chain = (i % 2) ? vc_orExpr(vc, v, chain) : vc_andExpr(vc, v, chain);
  }
  Expr simplified = vc_simplify(vc, chain);
  EXPECT_EQ(OR, getExprKind(simplified));
  vc_DeleteExpr(simplified);
  vc_assertFormula(vc, chain);
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  Expr value = vc_getCounterExample(vc, chain);
  EXPECT_EQ(TRUE, getExprKind(value));
  vc_DeleteExpr(value);
  vc_Destroy(vc);
}

// 2.x gave each vc_parseExpr/vc_parseMemExpr its own declaration scope, so a
// text declares what it uses and a name the checker already has is simply the
// same symbol again: the same text parsed twice, a text declaring a symbol
// vc_varExpr made, an SMT-LIB 1 benchmark parsed twice. libstp2 seeded the
// checker's names into the parse, and the declaration of one was a syntax
// error, fatal by default. A re-declaration at another width -- a new symbol
// in 2.x -- is refused (lib/Compat2/NOTES.md).
TEST(libstp2_fidelity, a_parse_may_declare_a_name_the_checker_has)
{
  VC vc = vc_createValidityChecker();
  const char* text = "x : BITVECTOR(8); ASSERT(x = 0hex01); QUERY(x = 0hex02);";
  for (int round = 0; round < 2; ++round)
  {
    Expr query = nullptr, asserts = nullptr;
    ASSERT_EQ(1, vc_parseMemExpr(vc, text, &query, &asserts)) << round;
    EXPECT_EQ(0, vc_query(vc, query)) << round; // x = 1 makes x = 2 invalid
    vc_DeleteExpr(query);
    vc_DeleteExpr(asserts);
  }
  vc_Destroy(vc);

  vc = vc_createValidityChecker();
  Expr x = vc_varExpr(vc, "x", vc_bvType(vc, 8));
  vc_assertFormula(vc, vc_eqExpr(vc, x, vc_bvConstExprFromInt(vc, 8, 2)));
  Expr query = nullptr, asserts = nullptr;
  ASSERT_EQ(1, vc_parseMemExpr(vc, "x : BITVECTOR(8); QUERY(x = 0hex02);", &query, &asserts));
  EXPECT_EQ(1, vc_query(vc, query)); // the text's x is the checker's
  vc_DeleteExpr(query);
  vc_DeleteExpr(asserts);
  vc_Destroy(vc);

  vc = vc_createValidityChecker();
  vc_setFlags(vc, 'm', 0); // SMT-LIB 1
  const char* benchmark = "(benchmark b :logic QF_BV :extrafuns ((y BitVec[8])) "
                          ":assumption (= y bv3[8]) :formula (= y bv3[8]))";
  for (int round = 0; round < 2; ++round)
  {
    Expr q = nullptr, a = nullptr;
    EXPECT_EQ(1, vc_parseMemExpr(vc, benchmark, &q, &a)) << round;
    vc_DeleteExpr(q);
    vc_DeleteExpr(a);
  }
  vc_Destroy(vc);

  // at another width: refused, through the handler
  vc_registerErrorHandler(count_parse_error);
  vc_setErrorPolicy(STP_ON_ERROR_RETURN);
  vc = vc_createValidityChecker();
  parse_errors = 0;
  Expr q = nullptr, a = nullptr;
  ASSERT_EQ(1, vc_parseMemExpr(vc, "x : BITVECTOR(8); QUERY(x = 0hex02);", &q, &a));
  vc_DeleteExpr(q);
  vc_DeleteExpr(a);
  q = a = nullptr;
  EXPECT_NE(1, vc_parseMemExpr(vc, "x : BITVECTOR(4); QUERY(x = 0hex2);", &q, &a));
  EXPECT_EQ(1, parse_errors);
  vc_Destroy(vc);
  vc_setErrorPolicy(STP_ON_ERROR_ABORT);
  vc_registerErrorHandler(nullptr);
}

// 2.x applied a term-abstraction profile as its schema groups and its round
// ceiling, a half the caller named explicitly winning in either order. libstp2
// set the 3.x profile entry, which excludes the other two, and the checker died
// at its first assertion with "cannot be combined".
TEST(libstp2_fidelity, a_profile_and_an_explicit_half_combine)
{
  enum class Order
  {
    profile_rounds,
    rounds_profile,
    groups_profile,
    profile_after_query
  };
  for (Order order : {Order::profile_rounds, Order::rounds_profile, Order::groups_profile,
                      Order::profile_after_query})
  {
    VC vc = vc_createValidityChecker();
    switch (order)
    {
      case Order::profile_rounds:
        vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION, 1);
        vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_PROFILE, STP_BV_TERM_ABSTRACTION_PROFILE_AGGRESSIVE);
        vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_ROUNDS, 3);
        break;
      case Order::rounds_profile:
        vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION, 1);
        vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_ROUNDS, 3);
        vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_PROFILE, STP_BV_TERM_ABSTRACTION_PROFILE_AGGRESSIVE);
        break;
      case Order::groups_profile:
        vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION, 1);
        EXPECT_EQ(1, vc_setSchemaGroups(vc, "base,mul8"));
        vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_PROFILE, STP_BV_TERM_ABSTRACTION_PROFILE_BROAD);
        break;
      case Order::profile_after_query:
        EXPECT_EQ(1, vc_query(vc, vc_trueExpr(vc)));
        vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_PROFILE, STP_BV_TERM_ABSTRACTION_PROFILE_AGGRESSIVE);
        vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_ROUNDS, 3);
        break;
    }
    Type bv8 = vc_bvType(vc, 8);
    Expr x = vc_varExpr(vc, "x", bv8), y = vc_varExpr(vc, "y", bv8);
    vc_assertFormula(vc, vc_eqExpr(vc, vc_bvMultExpr(vc, 8, x, y), vc_bvConstExprFromInt(vc, 8, 6)));
    EXPECT_EQ(0, vc_query(vc, vc_falseExpr(vc))) << static_cast<int>(order);
    vc_Destroy(vc);
  }
}

// A vc_query_with_timeout that refuses its budget leaves the previous model
// readable, as 2.x did: the arguments are checked before the model goes.
TEST(libstp2_fidelity, a_refused_query_keeps_the_model)
{
  VC vc = vc_createValidityChecker();
  Expr x = vc_varExpr(vc, "x", vc_bvType(vc, 8));
  vc_assertFormula(vc, vc_eqExpr(vc, x, vc_bvConstExprFromInt(vc, 8, 0xAA)));
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  EXPECT_EQ(2, vc_query_with_timeout(vc, vc_falseExpr(vc), -5, -1));
  Expr v = vc_getCounterExample(vc, x);
  ASSERT_NE(nullptr, v);
  EXPECT_EQ(0xAAu, getBVUnsigned(v));
  vc_DeleteExpr(v);
  vc_Destroy(vc);
}

// 2.x kept an extract's bounds, and a sign extension's result width, as 32-bit
// constant children after the operand, which tree walkers read through
// getDegree and getChild.
TEST(libstp2_fidelity, extract_bounds_are_children)
{
  VC vc = vc_createValidityChecker();
  Expr x = vc_varExpr(vc, "x", vc_bvType(vc, 8));
  Expr ex = vc_bvExtract(vc, x, 5, 2);
  ASSERT_EQ(3, getDegree(ex));
  EXPECT_EQ(5u, getBVUnsigned(getChild(ex, 1)));
  EXPECT_EQ(2u, getBVUnsigned(getChild(ex, 2)));
  Expr sx = vc_bvSignExtend(vc, x, 16);
  ASSERT_EQ(2, getDegree(sx));
  EXPECT_EQ(16u, getBVUnsigned(getChild(sx, 1)));
  EXPECT_EQ(32, getBVLength(getChild(sx, 1)));
  vc_Destroy(vc);
}

// A parsed CVC query becomes the checker's query, which vc_printQuery prints,
// as 2.x's parser made it with SetQuery.
TEST(libstp2_fidelity, print_query_after_a_parse)
{
  VC vc = vc_createValidityChecker();
  Expr pq = nullptr, pa = nullptr;
  ASSERT_EQ(1, vc_parseMemExpr(vc, "p : BITVECTOR(8); QUERY(p = 0hex02);", &pq, &pa));
  testing::internal::CaptureStdout();
  vc_printQuery(vc);
  const std::string printed = testing::internal::GetCapturedStdout();
  EXPECT_NE(std::string::npos, printed.find("QUERY((p = 0x02")) << printed;
  vc_DeleteExpr(pq);
  vc_DeleteExpr(pa);
  vc_Destroy(vc);
}

// Counters live for the checker: a before-first-check option set after a
// query rebuilds the solver, and the count goes on from where it was.
TEST(libstp2_fidelity, counters_survive_a_rebuilt_solver)
{
  VC vc = vc_createValidityChecker();
  Type bv8 = vc_bvType(vc, 8);
  Expr a = vc_varExpr(vc, "a", bv8), b = vc_varExpr(vc, "b", bv8);
  vc_assertFormula(vc, vc_eqExpr(vc, vc_bvMultExpr(vc, 8, a, b), vc_bvConstExprFromInt(vc, 8, 6)));
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  const unsigned long long before = vc_getCounter(vc, STP_COUNTER_QUERIES_BITBLASTED);
  vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION, 1);
  EXPECT_EQ(before, vc_getCounter(vc, STP_COUNTER_QUERIES_BITBLASTED));
  vc_Destroy(vc);
}

namespace
{
int handler_calls = 0;
void count_handler_calls(const char*)
{
  ++handler_calls;
}
} // namespace

// Under STP_ON_ERROR_RETURN a misuse reaches the handler once: a null Expr
// given to vc_printBVBitStringToBuffer was reported by the Expr check and again
// by the function itself.
TEST(libstp2_fidelity, a_misuse_is_reported_once)
{
  vc_registerErrorHandler(count_handler_calls);
  vc_setErrorPolicy(STP_ON_ERROR_RETURN);
  handler_calls = 0;
  char* buf = nullptr;
  size_t len = 0;
  vc_printBVBitStringToBuffer(nullptr, &buf, &len);
  EXPECT_EQ(1, handler_calls);
  std::free(buf);
  vc_setErrorPolicy(STP_ON_ERROR_ABORT);
  vc_registerErrorHandler(nullptr);
}
