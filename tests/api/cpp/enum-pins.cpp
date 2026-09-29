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

// enum-pins.cpp -- the values of Kind and Option, and of stp_kind and
// stp_option, are pinned: a client compiled against one release reads the
// same kinds and options from the next. Each was recorded here when the
// tables gained explicit ids; a later entry adds its own line, and none of
// these lines ever changes.

#include "api_common.hpp"

#include <stp/stp.h>

using namespace stp;

TEST(EnumPins, every_kind_keeps_its_value)
{
  EXPECT_EQ(static_cast<int>(Kind::VALUE), 0);
  EXPECT_EQ(STP_KIND_VALUE, 0);
  EXPECT_EQ(static_cast<int>(Kind::CONSTANT), 1);
  EXPECT_EQ(STP_KIND_CONSTANT, 1);
  EXPECT_EQ(static_cast<int>(Kind::ITE), 2);
  EXPECT_EQ(STP_KIND_ITE, 2);
  EXPECT_EQ(static_cast<int>(Kind::EQUAL), 3);
  EXPECT_EQ(STP_KIND_EQUAL, 3);
  EXPECT_EQ(static_cast<int>(Kind::DISTINCT), 4);
  EXPECT_EQ(STP_KIND_DISTINCT, 4);
  EXPECT_EQ(static_cast<int>(Kind::APPLY), 5);
  EXPECT_EQ(STP_KIND_APPLY, 5);
  EXPECT_EQ(static_cast<int>(Kind::NOT), 6);
  EXPECT_EQ(STP_KIND_NOT, 6);
  EXPECT_EQ(static_cast<int>(Kind::AND), 7);
  EXPECT_EQ(STP_KIND_AND, 7);
  EXPECT_EQ(static_cast<int>(Kind::OR), 8);
  EXPECT_EQ(STP_KIND_OR, 8);
  EXPECT_EQ(static_cast<int>(Kind::XOR), 9);
  EXPECT_EQ(STP_KIND_XOR, 9);
  EXPECT_EQ(static_cast<int>(Kind::IMPLIES), 10);
  EXPECT_EQ(STP_KIND_IMPLIES, 10);
  EXPECT_EQ(static_cast<int>(Kind::BV_NOT), 11);
  EXPECT_EQ(STP_KIND_BV_NOT, 11);
  EXPECT_EQ(static_cast<int>(Kind::BV_AND), 12);
  EXPECT_EQ(STP_KIND_BV_AND, 12);
  EXPECT_EQ(static_cast<int>(Kind::BV_OR), 13);
  EXPECT_EQ(STP_KIND_BV_OR, 13);
  EXPECT_EQ(static_cast<int>(Kind::BV_XOR), 14);
  EXPECT_EQ(STP_KIND_BV_XOR, 14);
  EXPECT_EQ(static_cast<int>(Kind::BV_NAND), 15);
  EXPECT_EQ(STP_KIND_BV_NAND, 15);
  EXPECT_EQ(static_cast<int>(Kind::BV_NOR), 16);
  EXPECT_EQ(STP_KIND_BV_NOR, 16);
  EXPECT_EQ(static_cast<int>(Kind::BV_XNOR), 17);
  EXPECT_EQ(STP_KIND_BV_XNOR, 17);
  EXPECT_EQ(static_cast<int>(Kind::BV_NEG), 18);
  EXPECT_EQ(STP_KIND_BV_NEG, 18);
  EXPECT_EQ(static_cast<int>(Kind::BV_ADD), 19);
  EXPECT_EQ(STP_KIND_BV_ADD, 19);
  EXPECT_EQ(static_cast<int>(Kind::BV_SUB), 20);
  EXPECT_EQ(STP_KIND_BV_SUB, 20);
  EXPECT_EQ(static_cast<int>(Kind::BV_MUL), 21);
  EXPECT_EQ(STP_KIND_BV_MUL, 21);
  EXPECT_EQ(static_cast<int>(Kind::BV_UDIV), 22);
  EXPECT_EQ(STP_KIND_BV_UDIV, 22);
  EXPECT_EQ(static_cast<int>(Kind::BV_UREM), 23);
  EXPECT_EQ(STP_KIND_BV_UREM, 23);
  EXPECT_EQ(static_cast<int>(Kind::BV_SDIV), 24);
  EXPECT_EQ(STP_KIND_BV_SDIV, 24);
  EXPECT_EQ(static_cast<int>(Kind::BV_SREM), 25);
  EXPECT_EQ(STP_KIND_BV_SREM, 25);
  EXPECT_EQ(static_cast<int>(Kind::BV_SMOD), 26);
  EXPECT_EQ(STP_KIND_BV_SMOD, 26);
  EXPECT_EQ(static_cast<int>(Kind::BV_SHL), 27);
  EXPECT_EQ(STP_KIND_BV_SHL, 27);
  EXPECT_EQ(static_cast<int>(Kind::BV_LSHR), 28);
  EXPECT_EQ(STP_KIND_BV_LSHR, 28);
  EXPECT_EQ(static_cast<int>(Kind::BV_ASHR), 29);
  EXPECT_EQ(STP_KIND_BV_ASHR, 29);
  EXPECT_EQ(static_cast<int>(Kind::BV_CONCAT), 30);
  EXPECT_EQ(STP_KIND_BV_CONCAT, 30);
  EXPECT_EQ(static_cast<int>(Kind::BV_EXTRACT), 31);
  EXPECT_EQ(STP_KIND_BV_EXTRACT, 31);
  EXPECT_EQ(static_cast<int>(Kind::BV_ZERO_EXTEND), 32);
  EXPECT_EQ(STP_KIND_BV_ZERO_EXTEND, 32);
  EXPECT_EQ(static_cast<int>(Kind::BV_SIGN_EXTEND), 33);
  EXPECT_EQ(STP_KIND_BV_SIGN_EXTEND, 33);
  EXPECT_EQ(static_cast<int>(Kind::BV_REPEAT), 34);
  EXPECT_EQ(STP_KIND_BV_REPEAT, 34);
  EXPECT_EQ(static_cast<int>(Kind::BV_ROTATE_LEFT), 35);
  EXPECT_EQ(STP_KIND_BV_ROTATE_LEFT, 35);
  EXPECT_EQ(static_cast<int>(Kind::BV_ROTATE_RIGHT), 36);
  EXPECT_EQ(STP_KIND_BV_ROTATE_RIGHT, 36);
  EXPECT_EQ(static_cast<int>(Kind::BV_COMP), 37);
  EXPECT_EQ(STP_KIND_BV_COMP, 37);
  EXPECT_EQ(static_cast<int>(Kind::BV_ULT), 38);
  EXPECT_EQ(STP_KIND_BV_ULT, 38);
  EXPECT_EQ(static_cast<int>(Kind::BV_ULE), 39);
  EXPECT_EQ(STP_KIND_BV_ULE, 39);
  EXPECT_EQ(static_cast<int>(Kind::BV_UGT), 40);
  EXPECT_EQ(STP_KIND_BV_UGT, 40);
  EXPECT_EQ(static_cast<int>(Kind::BV_UGE), 41);
  EXPECT_EQ(STP_KIND_BV_UGE, 41);
  EXPECT_EQ(static_cast<int>(Kind::BV_SLT), 42);
  EXPECT_EQ(STP_KIND_BV_SLT, 42);
  EXPECT_EQ(static_cast<int>(Kind::BV_SLE), 43);
  EXPECT_EQ(STP_KIND_BV_SLE, 43);
  EXPECT_EQ(static_cast<int>(Kind::BV_SGT), 44);
  EXPECT_EQ(STP_KIND_BV_SGT, 44);
  EXPECT_EQ(static_cast<int>(Kind::BV_SGE), 45);
  EXPECT_EQ(STP_KIND_BV_SGE, 45);
  EXPECT_EQ(static_cast<int>(Kind::BV_UADDO), 46);
  EXPECT_EQ(STP_KIND_BV_UADDO, 46);
  EXPECT_EQ(static_cast<int>(Kind::BV_SADDO), 47);
  EXPECT_EQ(STP_KIND_BV_SADDO, 47);
  EXPECT_EQ(static_cast<int>(Kind::BV_UMULO), 48);
  EXPECT_EQ(STP_KIND_BV_UMULO, 48);
  EXPECT_EQ(static_cast<int>(Kind::BV_SMULO), 49);
  EXPECT_EQ(STP_KIND_BV_SMULO, 49);
  EXPECT_EQ(static_cast<int>(Kind::BV_USUBO), 50);
  EXPECT_EQ(STP_KIND_BV_USUBO, 50);
  EXPECT_EQ(static_cast<int>(Kind::BV_SSUBO), 51);
  EXPECT_EQ(STP_KIND_BV_SSUBO, 51);
  EXPECT_EQ(static_cast<int>(Kind::BV_NEGO), 52);
  EXPECT_EQ(STP_KIND_BV_NEGO, 52);
  EXPECT_EQ(static_cast<int>(Kind::BV_SDIVO), 53);
  EXPECT_EQ(STP_KIND_BV_SDIVO, 53);
  EXPECT_EQ(static_cast<int>(Kind::BV_REDAND), 54);
  EXPECT_EQ(STP_KIND_BV_REDAND, 54);
  EXPECT_EQ(static_cast<int>(Kind::BV_REDOR), 55);
  EXPECT_EQ(STP_KIND_BV_REDOR, 55);
  EXPECT_EQ(static_cast<int>(Kind::SELECT), 56);
  EXPECT_EQ(STP_KIND_SELECT, 56);
  EXPECT_EQ(static_cast<int>(Kind::STORE), 57);
  EXPECT_EQ(STP_KIND_STORE, 57);
  EXPECT_EQ(static_cast<int>(Kind::CONST_ARRAY), 58);
  EXPECT_EQ(STP_KIND_CONST_ARRAY, 58);
  EXPECT_EQ(static_cast<int>(Kind::FP_ABS), 59);
  EXPECT_EQ(STP_KIND_FP_ABS, 59);
  EXPECT_EQ(static_cast<int>(Kind::FP_NEG), 60);
  EXPECT_EQ(STP_KIND_FP_NEG, 60);
  EXPECT_EQ(static_cast<int>(Kind::FP_ADD), 61);
  EXPECT_EQ(STP_KIND_FP_ADD, 61);
  EXPECT_EQ(static_cast<int>(Kind::FP_SUB), 62);
  EXPECT_EQ(STP_KIND_FP_SUB, 62);
  EXPECT_EQ(static_cast<int>(Kind::FP_MUL), 63);
  EXPECT_EQ(STP_KIND_FP_MUL, 63);
  EXPECT_EQ(static_cast<int>(Kind::FP_DIV), 64);
  EXPECT_EQ(STP_KIND_FP_DIV, 64);
  EXPECT_EQ(static_cast<int>(Kind::FP_FMA), 65);
  EXPECT_EQ(STP_KIND_FP_FMA, 65);
  EXPECT_EQ(static_cast<int>(Kind::FP_SQRT), 66);
  EXPECT_EQ(STP_KIND_FP_SQRT, 66);
  EXPECT_EQ(static_cast<int>(Kind::FP_REM), 67);
  EXPECT_EQ(STP_KIND_FP_REM, 67);
  EXPECT_EQ(static_cast<int>(Kind::FP_RTI), 68);
  EXPECT_EQ(STP_KIND_FP_RTI, 68);
  EXPECT_EQ(static_cast<int>(Kind::FP_MIN), 69);
  EXPECT_EQ(STP_KIND_FP_MIN, 69);
  EXPECT_EQ(static_cast<int>(Kind::FP_MAX), 70);
  EXPECT_EQ(STP_KIND_FP_MAX, 70);
  EXPECT_EQ(static_cast<int>(Kind::FP_EQ), 71);
  EXPECT_EQ(STP_KIND_FP_EQ, 71);
  EXPECT_EQ(static_cast<int>(Kind::FP_LT), 72);
  EXPECT_EQ(STP_KIND_FP_LT, 72);
  EXPECT_EQ(static_cast<int>(Kind::FP_LEQ), 73);
  EXPECT_EQ(STP_KIND_FP_LEQ, 73);
  EXPECT_EQ(static_cast<int>(Kind::FP_GT), 74);
  EXPECT_EQ(STP_KIND_FP_GT, 74);
  EXPECT_EQ(static_cast<int>(Kind::FP_GEQ), 75);
  EXPECT_EQ(STP_KIND_FP_GEQ, 75);
  EXPECT_EQ(static_cast<int>(Kind::FP_IS_NORMAL), 76);
  EXPECT_EQ(STP_KIND_FP_IS_NORMAL, 76);
  EXPECT_EQ(static_cast<int>(Kind::FP_IS_SUBNORMAL), 77);
  EXPECT_EQ(STP_KIND_FP_IS_SUBNORMAL, 77);
  EXPECT_EQ(static_cast<int>(Kind::FP_IS_ZERO), 78);
  EXPECT_EQ(STP_KIND_FP_IS_ZERO, 78);
  EXPECT_EQ(static_cast<int>(Kind::FP_IS_INF), 79);
  EXPECT_EQ(STP_KIND_FP_IS_INF, 79);
  EXPECT_EQ(static_cast<int>(Kind::FP_IS_NAN), 80);
  EXPECT_EQ(STP_KIND_FP_IS_NAN, 80);
  EXPECT_EQ(static_cast<int>(Kind::FP_IS_NEG), 81);
  EXPECT_EQ(STP_KIND_FP_IS_NEG, 81);
  EXPECT_EQ(static_cast<int>(Kind::FP_IS_POS), 82);
  EXPECT_EQ(STP_KIND_FP_IS_POS, 82);
  EXPECT_EQ(static_cast<int>(Kind::FP_FP), 83);
  EXPECT_EQ(STP_KIND_FP_FP, 83);
  EXPECT_EQ(static_cast<int>(Kind::FP_TO_FP_FROM_BV), 84);
  EXPECT_EQ(STP_KIND_FP_TO_FP_FROM_BV, 84);
  EXPECT_EQ(static_cast<int>(Kind::FP_TO_FP_FROM_FP), 85);
  EXPECT_EQ(STP_KIND_FP_TO_FP_FROM_FP, 85);
  EXPECT_EQ(static_cast<int>(Kind::FP_TO_FP_FROM_SBV), 86);
  EXPECT_EQ(STP_KIND_FP_TO_FP_FROM_SBV, 86);
  EXPECT_EQ(static_cast<int>(Kind::FP_TO_FP_FROM_UBV), 87);
  EXPECT_EQ(STP_KIND_FP_TO_FP_FROM_UBV, 87);
  EXPECT_EQ(static_cast<int>(Kind::FP_TO_FP_FROM_REAL), 88);
  EXPECT_EQ(STP_KIND_FP_TO_FP_FROM_REAL, 88);
  EXPECT_EQ(static_cast<int>(Kind::FP_TO_UBV), 89);
  EXPECT_EQ(STP_KIND_FP_TO_UBV, 89);
  EXPECT_EQ(static_cast<int>(Kind::FP_TO_SBV), 90);
  EXPECT_EQ(STP_KIND_FP_TO_SBV, 90);
  EXPECT_EQ(static_cast<int>(Kind::FP_TO_REAL), 91);
  EXPECT_EQ(STP_KIND_FP_TO_REAL, 91);
  EXPECT_EQ(static_cast<int>(Kind::FP_TO_IEEE_BV), 92);
  EXPECT_EQ(STP_KIND_FP_TO_IEEE_BV, 92);
  EXPECT_EQ(static_cast<int>(Kind::REAL_ADD), 93);
  EXPECT_EQ(STP_KIND_REAL_ADD, 93);
  EXPECT_EQ(static_cast<int>(Kind::REAL_SUB), 94);
  EXPECT_EQ(STP_KIND_REAL_SUB, 94);
  EXPECT_EQ(static_cast<int>(Kind::REAL_NEG), 95);
  EXPECT_EQ(STP_KIND_REAL_NEG, 95);
  EXPECT_EQ(static_cast<int>(Kind::REAL_MUL), 96);
  EXPECT_EQ(STP_KIND_REAL_MUL, 96);
  EXPECT_EQ(static_cast<int>(Kind::REAL_DIV), 97);
  EXPECT_EQ(STP_KIND_REAL_DIV, 97);
  EXPECT_EQ(static_cast<int>(Kind::REAL_LT), 98);
  EXPECT_EQ(STP_KIND_REAL_LT, 98);
  EXPECT_EQ(static_cast<int>(Kind::REAL_LE), 99);
  EXPECT_EQ(STP_KIND_REAL_LE, 99);
  EXPECT_EQ(static_cast<int>(Kind::REAL_GT), 100);
  EXPECT_EQ(STP_KIND_REAL_GT, 100);
  EXPECT_EQ(static_cast<int>(Kind::REAL_GE), 101);
  EXPECT_EQ(STP_KIND_REAL_GE, 101);
  EXPECT_GE(static_cast<int>(Kind::NUM_KINDS), 102);
}

TEST(EnumPins, every_stable_option_keeps_its_value_and_name)
{
  EXPECT_EQ(static_cast<int>(Option::PRODUCE_MODELS), 0);
  EXPECT_EQ(STP_OPT_PRODUCE_MODELS, 0);
  EXPECT_EQ(Options::name_of(Option::PRODUCE_MODELS), "produce-models");
  EXPECT_EQ(Options::stable_option("produce-models"), Option::PRODUCE_MODELS);
  EXPECT_STREQ(stp_option_name(STP_OPT_PRODUCE_MODELS), "produce-models");
  EXPECT_EQ(static_cast<int>(Option::SAT_BACKEND), 1);
  EXPECT_EQ(STP_OPT_SAT_BACKEND, 1);
  EXPECT_EQ(Options::name_of(Option::SAT_BACKEND), "sat-backend");
  EXPECT_EQ(Options::stable_option("sat-backend"), Option::SAT_BACKEND);
  EXPECT_STREQ(stp_option_name(STP_OPT_SAT_BACKEND), "sat-backend");
  EXPECT_EQ(static_cast<int>(Option::RANDOM_SEED), 2);
  EXPECT_EQ(STP_OPT_RANDOM_SEED, 2);
  EXPECT_EQ(Options::name_of(Option::RANDOM_SEED), "random-seed");
  EXPECT_EQ(Options::stable_option("random-seed"), Option::RANDOM_SEED);
  EXPECT_STREQ(stp_option_name(STP_OPT_RANDOM_SEED), "random-seed");
  EXPECT_EQ(static_cast<int>(Option::MODEL_ARRAY_FILL), 3);
  EXPECT_EQ(STP_OPT_MODEL_ARRAY_FILL, 3);
  EXPECT_EQ(Options::name_of(Option::MODEL_ARRAY_FILL), "model-array-fill");
  EXPECT_EQ(Options::stable_option("model-array-fill"), Option::MODEL_ARRAY_FILL);
  EXPECT_STREQ(stp_option_name(STP_OPT_MODEL_ARRAY_FILL), "model-array-fill");
  EXPECT_EQ(static_cast<int>(Option::LOGIC), 4);
  EXPECT_EQ(STP_OPT_LOGIC, 4);
  EXPECT_EQ(Options::name_of(Option::LOGIC), "logic");
  EXPECT_EQ(Options::stable_option("logic"), Option::LOGIC);
  EXPECT_STREQ(stp_option_name(STP_OPT_LOGIC), "logic");
  EXPECT_EQ(static_cast<int>(Option::SIMPLIFY), 5);
  EXPECT_EQ(STP_OPT_SIMPLIFY, 5);
  EXPECT_EQ(Options::name_of(Option::SIMPLIFY), "simplify");
  EXPECT_EQ(Options::stable_option("simplify"), Option::SIMPLIFY);
  EXPECT_STREQ(stp_option_name(STP_OPT_SIMPLIFY), "simplify");
  EXPECT_EQ(static_cast<int>(Option::DEFAULT_ROUNDING_MODE), 6);
  EXPECT_EQ(STP_OPT_DEFAULT_ROUNDING_MODE, 6);
  EXPECT_EQ(Options::name_of(Option::DEFAULT_ROUNDING_MODE), "default-rounding-mode");
  EXPECT_EQ(Options::stable_option("default-rounding-mode"), Option::DEFAULT_ROUNDING_MODE);
  EXPECT_STREQ(stp_option_name(STP_OPT_DEFAULT_ROUNDING_MODE), "default-rounding-mode");
  EXPECT_EQ(static_cast<int>(Option::DISABLE_SIMPLIFICATIONS), 7);
  EXPECT_EQ(STP_OPT_DISABLE_SIMPLIFICATIONS, 7);
  EXPECT_EQ(Options::name_of(Option::DISABLE_SIMPLIFICATIONS), "disable-simplifications");
  EXPECT_EQ(Options::stable_option("disable-simplifications"), Option::DISABLE_SIMPLIFICATIONS);
  EXPECT_STREQ(stp_option_name(STP_OPT_DISABLE_SIMPLIFICATIONS), "disable-simplifications");
  EXPECT_EQ(static_cast<int>(Option::THREADS), 8);
  EXPECT_EQ(STP_OPT_THREADS, 8);
  EXPECT_EQ(Options::name_of(Option::THREADS), "threads");
  EXPECT_EQ(Options::stable_option("threads"), Option::THREADS);
  EXPECT_STREQ(stp_option_name(STP_OPT_THREADS), "threads");
  EXPECT_EQ(static_cast<int>(Option::ARRAY_EQUALITY), 9);
  EXPECT_EQ(STP_OPT_ARRAY_EQUALITY, 9);
  EXPECT_EQ(Options::name_of(Option::ARRAY_EQUALITY), "array-equality");
  EXPECT_EQ(Options::stable_option("array-equality"), Option::ARRAY_EQUALITY);
  EXPECT_STREQ(stp_option_name(STP_OPT_ARRAY_EQUALITY), "array-equality");
  EXPECT_EQ(static_cast<int>(Option::BV_EQ_ABSTRACTION), 10);
  EXPECT_EQ(STP_OPT_BV_EQ_ABSTRACTION, 10);
  EXPECT_EQ(Options::name_of(Option::BV_EQ_ABSTRACTION), "bv-eq-abstraction");
  EXPECT_EQ(Options::stable_option("bv-eq-abstraction"), Option::BV_EQ_ABSTRACTION);
  EXPECT_STREQ(stp_option_name(STP_OPT_BV_EQ_ABSTRACTION), "bv-eq-abstraction");
  EXPECT_EQ(static_cast<int>(Option::BV_TERM_ABSTRACTION), 11);
  EXPECT_EQ(STP_OPT_BV_TERM_ABSTRACTION, 11);
  EXPECT_EQ(Options::name_of(Option::BV_TERM_ABSTRACTION), "bv-term-abstraction");
  EXPECT_EQ(Options::stable_option("bv-term-abstraction"), Option::BV_TERM_ABSTRACTION);
  EXPECT_STREQ(stp_option_name(STP_OPT_BV_TERM_ABSTRACTION), "bv-term-abstraction");
  EXPECT_EQ(static_cast<int>(Option::UNINTERPRETED_FUNCTIONS), 12);
  EXPECT_EQ(STP_OPT_UNINTERPRETED_FUNCTIONS, 12);
  EXPECT_EQ(Options::name_of(Option::UNINTERPRETED_FUNCTIONS), "uninterpreted-functions");
  EXPECT_EQ(Options::stable_option("uninterpreted-functions"), Option::UNINTERPRETED_FUNCTIONS);
  EXPECT_STREQ(stp_option_name(STP_OPT_UNINTERPRETED_FUNCTIONS), "uninterpreted-functions");
  EXPECT_EQ(static_cast<int>(Option::UF_ACKERMANN), 13);
  EXPECT_EQ(STP_OPT_UF_ACKERMANN, 13);
  EXPECT_EQ(Options::name_of(Option::UF_ACKERMANN), "uf-ackermann");
  EXPECT_EQ(Options::stable_option("uf-ackermann"), Option::UF_ACKERMANN);
  EXPECT_STREQ(stp_option_name(STP_OPT_UF_ACKERMANN), "uf-ackermann");
  EXPECT_EQ(static_cast<int>(Option::UF_SORT_WIDTH), 14);
  EXPECT_EQ(STP_OPT_UF_SORT_WIDTH, 14);
  EXPECT_EQ(Options::name_of(Option::UF_SORT_WIDTH), "uf-sort-width");
  EXPECT_EQ(Options::stable_option("uf-sort-width"), Option::UF_SORT_WIDTH);
  EXPECT_STREQ(stp_option_name(STP_OPT_UF_SORT_WIDTH), "uf-sort-width");
  EXPECT_EQ(static_cast<int>(Option::FP_ABSTRACTION), 15);
  EXPECT_EQ(STP_OPT_FP_ABSTRACTION, 15);
  EXPECT_EQ(Options::name_of(Option::FP_ABSTRACTION), "fp-abstraction");
  EXPECT_EQ(Options::stable_option("fp-abstraction"), Option::FP_ABSTRACTION);
  EXPECT_STREQ(stp_option_name(STP_OPT_FP_ABSTRACTION), "fp-abstraction");
  EXPECT_EQ(static_cast<int>(Option::CNF_GENERATION_EFFORT), 16);
  EXPECT_EQ(STP_OPT_CNF_GENERATION_EFFORT, 16);
  EXPECT_EQ(Options::name_of(Option::CNF_GENERATION_EFFORT), "cnf-generation-effort");
  EXPECT_EQ(Options::stable_option("cnf-generation-effort"), Option::CNF_GENERATION_EFFORT);
  EXPECT_STREQ(stp_option_name(STP_OPT_CNF_GENERATION_EFFORT), "cnf-generation-effort");
  EXPECT_EQ(static_cast<int>(Option::INCREMENTAL), 17);
  EXPECT_EQ(STP_OPT_INCREMENTAL, 17);
  EXPECT_EQ(Options::name_of(Option::INCREMENTAL), "incremental");
  EXPECT_EQ(Options::stable_option("incremental"), Option::INCREMENTAL);
  EXPECT_STREQ(stp_option_name(STP_OPT_INCREMENTAL), "incremental");
  EXPECT_EQ(static_cast<int>(Option::INCREMENTAL_AUTO_ENGAGE_AT), 18);
  EXPECT_EQ(STP_OPT_INCREMENTAL_AUTO_ENGAGE_AT, 18);
  EXPECT_EQ(Options::name_of(Option::INCREMENTAL_AUTO_ENGAGE_AT), "incremental-auto-engage-at");
  EXPECT_EQ(Options::stable_option("incremental-auto-engage-at"), Option::INCREMENTAL_AUTO_ENGAGE_AT);
  EXPECT_STREQ(stp_option_name(STP_OPT_INCREMENTAL_AUTO_ENGAGE_AT), "incremental-auto-engage-at");
  EXPECT_EQ(static_cast<int>(Option::MAX_NUM_CONFL), 19);
  EXPECT_EQ(STP_OPT_MAX_NUM_CONFL, 19);
  EXPECT_EQ(Options::name_of(Option::MAX_NUM_CONFL), "max-num-confl");
  EXPECT_EQ(Options::stable_option("max-num-confl"), Option::MAX_NUM_CONFL);
  EXPECT_STREQ(stp_option_name(STP_OPT_MAX_NUM_CONFL), "max-num-confl");
  EXPECT_EQ(static_cast<int>(Option::MAX_TIME), 20);
  EXPECT_EQ(STP_OPT_MAX_TIME, 20);
  EXPECT_EQ(Options::name_of(Option::MAX_TIME), "max-time");
  EXPECT_EQ(Options::stable_option("max-time"), Option::MAX_TIME);
  EXPECT_STREQ(stp_option_name(STP_OPT_MAX_TIME), "max-time");
  EXPECT_EQ(static_cast<int>(Option::CHECK_SANITY), 21);
  EXPECT_EQ(STP_OPT_CHECK_SANITY, 21);
  EXPECT_EQ(Options::name_of(Option::CHECK_SANITY), "check-sanity");
  EXPECT_EQ(Options::stable_option("check-sanity"), Option::CHECK_SANITY);
  EXPECT_STREQ(stp_option_name(STP_OPT_CHECK_SANITY), "check-sanity");
  EXPECT_GE(static_cast<int>(Option::NUM_STABLE_OPTIONS), 22);
}
