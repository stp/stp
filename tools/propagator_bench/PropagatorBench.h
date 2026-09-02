/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: July, 2026
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

// Shared types for the propagator benchmark. See README.md.

#ifndef PROPAGATOR_BENCH_H_
#define PROPAGATOR_BENCH_H_

#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/constantBitP/ConstantBitPropagation.h"
#include "stp/Simplifier/constantBitP/FixedBits.h"

#include <cstdint>
#include <random>
#include <string>
#include <vector>

namespace propbench
{
using simplifier::constantBitP::FixedBits;
using std::string;
using std::vector;

// ---------------------------------------------------------------------------
// The abstract domains that STP propagates over.

enum class Domain
{
  Cbitp,   // simplifier::constantBitP, the FixedBits transfer functions
  Interval, // stp::UnsignedIntervalAnalysis
  ValueSet  // stp::ValueSetAnalysis
};

// Which way information flows in the cases we hand the propagator. The
// constant-bit transfer functions are all "both ways" functions, so the
// direction here describes what is *seeded*, not what the code is able to
// deduce:
//   BottomUp  children partially known, result unknown
//   TopDown   result partially known, children unknown
//   BothWays  everything partially known
// The interval and value-set analyses only ever run bottom up.
enum class Direction
{
  BottomUp,
  TopDown,
  BothWays
};

const char* name(Domain d);
const char* name(Direction d);
bool parseDomain(const string& s, Domain& out);
bool parseDirection(const string& s, Direction& out);

// ---------------------------------------------------------------------------
// Operations.

// The shape of a node as a function of the benchmarked width w.
enum class Shape
{
  Nary,      // (w, w, ...) -> w
  Predicate, // (w, w) -> bool
  Unary,     // (w) -> w
  BoolNary,  // (bool, bool, ...) -> bool
  BoolUnary, // (bool) -> bool
  Ite,       // (bool, w, w) -> w
  Concat,    // (w/2, w/2) -> w
  Extract,   // (w, const, const) -> w/2
  Extend     // (w/2, const) -> w
};

struct ChildSpec
{
  unsigned width = 0;      // 1 for booleans
  bool isBoolean = false;
  // Structural children -- the bounds of an extract, the width of an
  // extend. They are always completely known and never propagated over.
  bool isConstant = false;
  uint64_t value = 0; // when isConstant
};

// One instance of an operation: the widths of its children and result.
struct Layout
{
  vector<ChildSpec> children;
  unsigned outWidth = 0;
  bool outIsBoolean = false;
  bool ok = false; // false when the operation can't be built at that width

  // Indices of the children the harness varies (i.e. not structural).
  vector<unsigned> varying() const;
  // Total width of the varying children; the semantics table is indexed by
  // their concatenated values, so this must stay small for the exhaustive
  // phases.
  unsigned packedBits() const;
};

struct OpSpec
{
  stp::Kind kind;
  const char* name; // as in SMT-LIB, e.g. "bvsgt"
  Shape shape;
  bool nary;         // whether the transfer function takes more than 2 children
  bool satCheckable; // maxPrecision() builds its node out of plain symbols,
                     // so operations with structural children are excluded
};

const vector<OpSpec>& allOps();
const OpSpec* findOp(const string& name);
bool supports(Domain d, const OpSpec& op);

// Builds the layout, expanding n-ary operations to `arity` children.
Layout layoutFor(const OpSpec& op, unsigned width, unsigned arity);

// A node of the right shape with a fresh symbol for every varying child.
// The interval and value-set transfer functions dispatch on the node, and
// the SAT-based precision check needs the same shape.
stp::ASTNode buildNode(stp::STPMgr* mgr, const OpSpec& op, const Layout& l);

// The reference semantics, from STP's constant evaluator. `values` holds one
// entry per child, structural children included.
uint64_t evaluate(stp::STPMgr* mgr, const OpSpec& op, const Layout& l,
                  const vector<uint64_t>& values);

// The same, for children that are already constant nodes. Widths above 64
// bits go through here.
stp::ASTNode evaluateNodes(stp::STPMgr* mgr, const OpSpec& op, const Layout& l,
                           const stp::ASTVec& children);

// evaluate() for every combination of the varying children's values, indexed
// by their concatenated values (child 0 in the least significant position).
// Only usable when packedBits() is small.
vector<uint64_t> semanticsTable(stp::STPMgr* mgr, const OpSpec& op,
                                const Layout& l);

// ---------------------------------------------------------------------------
// Results.

// Exhaustive comparison against a brute-forced maximally precise reference at
// a small width.
struct PrecisionResult
{
  bool ran = false;
  unsigned width = 0;
  uint64_t cases = 0;
  uint64_t precise = 0;         // cases where nothing more could be deduced
  uint64_t unsound = 0;         // cases where a real solution was excluded
  uint64_t missedConflict = 0;  // cases with no solution, not reported
  uint64_t derivable = 0;       // bits an ideal propagator would have deduced
  uint64_t gained = 0;          // bits this propagator deduced

  bool maximallyPrecise() const
  {
    return ran && cases > 0 && precise == cases && unsound == 0;
  }
};

// Spot check against maxPrecision() at the row's own width.
struct SatCheck
{
  bool ran = false;
  uint64_t cases = 0;
  uint64_t precise = 0;
  uint64_t unsound = 0;
};

// Comparison against unit propagation on the bit-blasted encoding: not what
// an ideal propagator could deduce, but what the SAT solver would have
// deduced from the same inputs without the propagator's help. Both figures
// are bits newly fixed, averaged per case, over the varying children and the
// result.
struct BcpCheck
{
  bool ran = false;
  uint64_t cases = 0;
  double bcpBits = 0;   // fixed by boolean constraint propagation
  double cbitpBits = 0; // fixed by the transfer function, same cases
  unsigned clauses = 0; // size of the encoding propagated over
  unsigned variables = 0;

  // What the propagator adds over the encoding. Above 1 it is earning its
  // keep; at 1 the SAT solver would have found the same bits anyway.
  double ratio() const
  {
    if (!ran || bcpBits <= 0)
      return cbitpBits > 0 ? 0 : 1; // 0 stands for "infinite", printed as such
    return cbitpBits / bcpBits;
  }
};

// Exhaustive arc-consistency check of the bit-blasted encoding at a small
// width: every combination of fixed/unfixed input bits, contradictory ones
// included, against a brute-forced ideal. This is the half the sampled
// --bcp-check cannot reach, because its cases are all built from a solution
// and so are never contradictory.
struct BcpExhaustive
{
  bool ran = false;
  unsigned width = 0;
  uint64_t cases = 0;
  uint64_t complete = 0;       // deduced everything that follows
  uint64_t incomplete = 0;     // left something on the table
  uint64_t missedConflict = 0; // no solution, and propagation did not say so
  uint64_t unsound = 0;        // fixed more than the ideal: would be a bug
  uint64_t contradictory = 0;  // cases with no solution at all
  uint64_t derivable = 0;
  uint64_t gained = 0;

  // Arc consistent means both halves: everything implied is derived, and
  // every contradiction is detected.
  bool arcConsistent() const
  {
    return ran && cases > 0 && incomplete == 0 && missedConflict == 0 &&
           unsound == 0;
  }
};

// Graded consistency of the bit-blasted encoding, from a self-contained unit
// propagator over the generated clauses (Consistency.cpp). Three claims,
// strongest last:
//   URC  unit propagation refutes every inconsistent partial assignment of
//        the operation's input/output bits
//   GAC  URC, and every implied input/output literal is derived
//   PC   both, quantified over every CNF variable, auxiliaries included
struct ConsistencyCheck
{
  bool ran = false;
  unsigned width = 0;
  unsigned clauses = 0;
  unsigned literals = 0;
  unsigned variables = 0; // CNF variables, auxiliaries included
  unsigned ioVars = 0;    // of them, input/output bits

  // Over the input/output variables, exhaustively.
  uint64_t ioCases = 0;
  uint64_t ioContradictory = 0;
  uint64_t gacIncomplete = 0; // cases that left an implied literal underived
  uint64_t gacDerivable = 0;  // implied literals over all consistent cases
  uint64_t gacDerived = 0;
  uint64_t urcMissed = 0; // contradictory cases unit propagation let through
  // urcMissed again, indexed by how many input/output bits the case left
  // unset. A miss at index 0 is a fully assigned contradiction the encoding
  // cannot see; misses only at high indices are the cheap kind.
  vector<uint64_t> urcMissedByUnset;
  uint64_t unsound = 0; // derived something no solution supports: a bug

  // Over every variable: exhaustive when 3^variables fits the cap, else
  // sampled -- a sample can prove PC absent, never present.
  bool pcRan = false;
  bool pcExhaustive = false;
  uint64_t pcCases = 0;
  uint64_t pcContradictory = 0;
  uint64_t pcIncomplete = 0;
  uint64_t pcDerivable = 0;
  uint64_t pcDerived = 0;
  uint64_t pcMissedConflict = 0;

  bool urc() const { return ran && urcMissed == 0 && unsound == 0; }
  bool gac() const { return urc() && gacIncomplete == 0; }
  bool pc() const
  {
    return gac() && pcRan && pcExhaustive && pcIncomplete == 0 &&
           pcMissedConflict == 0;
  }
};

struct Row
{
  Domain domain = Domain::Cbitp;
  string op;
  Direction direction = Direction::BottomUp;
  unsigned width = 0;
  unsigned arity = 2;
  string input;         // how the case was seeded, e.g. "50% fixed"
  unsigned prob = 0;    // percentage of bits seeded (cbitp, interval)
  unsigned setSize = 0; // values per input set (value set)
  bool implemented = true;

  double nsPerCall = 0;
  double opsPerSec = 0;
  double bitsGained = 0; // information deduced per call, in bits
  uint64_t calls = 0;
  uint64_t conflicts = 0;
  uint64_t witnessUnsound = 0; // cases whose known solution was excluded

  PrecisionResult precision; // exhaustive, at a small width
  SatCheck sat;              // at this row's width
  BcpCheck bcp;              // against the bit-blasted encoding
  BcpExhaustive bcpExhaustive; // arc consistency of that encoding
  ConsistencyCheck consistency; // graded GAC / URC / PC of that encoding
};

struct Config
{
  vector<Domain> domains;
  vector<string> ops; // empty means every operation
  vector<unsigned> widths{8, 16, 32, 64};
  vector<unsigned> probs{1, 50, 95};
  vector<unsigned> setSizes{2, 4, 8};
  vector<Direction> directions{Direction::BottomUp, Direction::BothWays};
  unsigned arity = 2;
  unsigned iterations = 20000;
  double budgetSeconds = 0.25;
  unsigned repeats = 3;
  bool precision = true;
  unsigned precisionWidth = 4;
  uint64_t precisionCaseCap = 4000000;
  unsigned satCases = 0;        // 0 disables the SAT spot check
  double satBudgetSeconds = 5;  // it is thousands of times slower per case
  unsigned bcpCases = 0;        // 0 disables the bit-blasted comparison
  double bcpBudgetSeconds = 5;  // a fresh solver and CNF load per case
  unsigned bcpExhaustiveWidth = 0; // 0 disables the arc-consistency check
  string dumpCnf;          // write the encoding as DIMACS here and exit
  unsigned dumpWidth = 64; // at this width
  unsigned consistencyWidth = 0;   // 0 disables the graded GAC/URC/PC check
  uint64_t consistencyCap = 20000000; // most exhaustive cases per scope
  uint64_t pcSamples = 1000000; // sampled cases when 3^vars exceeds the cap
  int adderVariant = -1;  // -1 leaves UserDefinedFlags::adder_variant alone
  int bvplusVariant = -1; // likewise bvplus_variant
  int divVariant1 = -1;   // likewise division_variant_1..4
  int divVariant2 = -1;
  int divVariant3 = -1;
  int divVariant4 = -1;
  int divLemmas = -1;     // likewise division_lemmas
  int divByMult = -1;     // likewise division_by_multiplication
  unsigned duelWidth = 0; // 0 disables the UP-vs-cbitp duel
  string duelDump;        // write asymmetric duel cases here
  unsigned seed = 42;
  // How the CNF that --bcp-check propagates over is generated. Empty leaves
  // STP's default (medium) alone. A different encoding of the same circuit
  // can have different unit-propagation strength, which is the point of
  // being able to set it here.
  string cnf;
  bool shiftBias = true; // draw half the shift amounts from [0, width)
  bool verbose = false;
  string html;
  string csv;
};

// The measured cost of one configuration, in the units the runners share.
struct Timing
{
  double nsPerCall = 0;
  uint64_t calls = 0;
  uint64_t conflicts = 0;
  uint64_t unsound = 0;
  double bitsGained = 0;
};

// ---------------------------------------------------------------------------
// Per-domain runners. Each appends its rows to `out`.

void runCbitp(stp::STPMgr* mgr, const Config& c, vector<Row>& out);
void runInterval(stp::STPMgr* mgr, const Config& c, vector<Row>& out);
void runValueSet(stp::STPMgr* mgr, const Config& c, vector<Row>& out);

// The constant-bit transfer function for a kind, exactly as
// ConstantBitPropagation::dispatchToTransferFunctions would call it.
simplifier::constantBitP::Result cbitpTransfer(stp::STPMgr* mgr, stp::Kind k,
                                               vector<FixedBits*>& children,
                                               FixedBits& output);

// ---------------------------------------------------------------------------
// The bit-blasted encoding, as a propagator. See Bcp.cpp. Built once per
// (operation, layout) because bit-blasting dwarfs the propagation; NULL when
// the operation cannot be encoded, or in a build without CryptoMiniSat.
// `bits` is always the varying children in layout order, then the result.

struct BcpEncoding;

bool bcpAvailable();
BcpEncoding* makeBcpEncoding(stp::STPMgr* mgr, const OpSpec& op,
                             const Layout& l);
void destroyBcpEncoding(BcpEncoding* e);
// Asserts the known bits and propagates. Returns false when unit propagation
// refutes them -- the conflict-detection half of arc consistency -- and
// otherwise sets `fixed` to the variables fixed at decision level zero.
bool bcpPropagate(const BcpEncoding* e, const vector<const FixedBits*>& bits,
                  unsigned& fixed);
// Of the known bits, how many the encoding represents at all.
unsigned bcpVisibleFixed(const BcpEncoding* e,
                         const vector<const FixedBits*>& bits);
// The size of the CNF being propagated over, which is what --cnf changes.
unsigned bcpClauses(const BcpEncoding* e);
unsigned bcpVariables(const BcpEncoding* e);

// The raw material the consistency checker propagates over itself: the
// clauses (literals encoded 2*variable+negated, variables from 1) and the SAT
// variable of every input/output bit -- the varying children in layout order,
// then the result, BCP_NOT_ENCODED for bits the CNF never saw. False in a
// build without CryptoMiniSat.
constexpr unsigned BCP_NOT_ENCODED = ~((unsigned)0);
bool bcpMaterial(const BcpEncoding* e, vector<vector<int>>& clauses,
                 vector<vector<unsigned>>& io, unsigned& variables);

// The graded GAC/URC/PC check, at cfg.consistencyWidth. See Consistency.cpp.
ConsistencyCheck consistencyCheck(stp::STPMgr* mgr, const OpSpec& op,
                                  const Config& cfg);

// Exhaustive per-state head-to-head at cfg.duelWidth: for every ternary
// partial assignment of the operation's input/output bits, compare what unit
// propagation on the bit-blasted CNF derives against what the constant-bit
// transfer function derives, refereed by the exact solution table. Prints a
// summary; returns false when the width does not fit under the caps.
bool duelCheck(stp::STPMgr* mgr, const OpSpec& op, const Config& cfg);

// Writes the encoding of op at cfg.dumpWidth as DIMACS, with `c sym` header
// lines mapping every input/output bit to its variable -- the varying
// children in layout order, then the result, 0 for a bit the CNF never saw.
// For drivers that append query clauses and hand the file to a SAT solver.
bool dumpEncoding(stp::STPMgr* mgr, const OpSpec& op, const Config& cfg,
                  const string& path);

// ---------------------------------------------------------------------------
// Reporting.

void printText(const Config& c, const vector<Row>& rows);
void writeCsv(const Config& c, const vector<Row>& rows, const string& path);
void writeHtml(const Config& c, const vector<Row>& rows, const string& path);

// ---------------------------------------------------------------------------
// Small shared helpers.

// A fully fixed FixedBits holding a random value (or the given one).
FixedBits randomConcrete(const ChildSpec& spec, std::mt19937& rand);
FixedBits concreteOf(const ChildSpec& spec, uint64_t value);
// Unfixes every bit with probability (100 - percent)%.
void unfixTo(FixedBits& bits, unsigned percent, std::mt19937& rand);
uint64_t unsignedValue(const FixedBits& bits);

double median(vector<double>& v);
} // namespace propbench

#endif
