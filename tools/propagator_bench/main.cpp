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

// How fast are STP's propagators, and how much do they deduce? See README.md.

#include "PropagatorBench.h"

#include "stp/Parser/LetMgr.h"
#include "stp/cpp_interface.h"

#include <cstdlib>
#include <cstring>
#include <iostream>
#include <sstream>

using namespace propbench;
using std::string;
using std::vector;

namespace
{

vector<string> split(const string& s)
{
  vector<string> parts;
  std::stringstream ss(s);
  string item;
  while (std::getline(ss, item, ','))
    if (!item.empty())
      parts.push_back(item);
  return parts;
}

vector<unsigned> splitNumbers(const string& s)
{
  vector<unsigned> parts;
  for (const string& item : split(s))
    parts.push_back((unsigned)strtoul(item.c_str(), NULL, 10));
  return parts;
}

void usage()
{
  std::cout
      << "usage: propagator_bench [options]\n\n"
      << "Measures the speed and the precision of STP's propagators.\n\n"
      << "  --domains LIST      cbitp,interval,valueset (default: all)\n"
      << "  --ops LIST          only these operations (default: all)\n"
      << "  --widths LIST       bit-widths to time at (default 8,16,32,64)\n"
      << "  --probs LIST        percentage of input bits known, for cbitp\n"
      << "                      and interval (default 1,50,95)\n"
      << "  --set-sizes LIST    values per input set, for valueset\n"
      << "                      (default 2,4,8)\n"
      << "  --directions LIST   bottom-up,top-down,both-ways -- what is\n"
      << "                      seeded (default bottom-up,both-ways).\n"
      << "                      Only cbitp propagates downwards.\n"
      << "  --arity N           children for the n-ary operations "
         "(default 2)\n"
      << "  --iterations N      cases per configuration (default 20000)\n"
      << "  --budget SECONDS    time limit per timed run (default 0.25)\n"
      << "  --repeats N         timed runs per configuration, the median is\n"
      << "                      reported (default 3)\n"
      << "  --precision-width W exhaustive precision width (default 4);\n"
      << "                      lowered automatically when too costly\n"
      << "  --no-precision      skip the exhaustive precision phase\n"
      << "  --sat-check N       also check N cases per row against the\n"
      << "                      SAT-based maxPrecision(), at the real width\n"
      << "  --sat-budget SECS   time limit for that check, per row\n"
      << "                      (default 5); fewer cases are run if it\n"
      << "                      doesn't fit\n"
      << "  --bcp-check N       also compare N cases per row against unit\n"
      << "                      propagation on the bit-blasted encoding --\n"
      << "                      what the SAT solver deduces without the\n"
      << "                      propagator (CryptoMiniSat builds only)\n"
      << "  --bcp-budget SECS   time limit for that comparison, per row\n"
      << "                      (default 5)\n"
      << "  --bcp-exhaustive W  check the bit-blasted encoding for arc\n"
      << "                      consistency at width W: every combination of\n"
      << "                      fixed bits, contradictory ones included\n"
      << "  --consistency W     grade the encoding at width W: URC (every\n"
      << "                      contradiction refuted by unit propagation),\n"
      << "                      GAC (and every implied input/output literal\n"
      << "                      derived), PC (both, over every CNF variable,\n"
      << "                      auxiliaries included), each with how close\n"
      << "  --consistency-cap N most exhaustive cases per scope (default\n"
      << "                      20000000); the PC scope samples past it\n"
      << "  --pc-samples N      sampled PC cases when over the cap\n"
      << "                      (default 1000000)\n"
      << "  --dump-cnf FILE     write the encoding of the one op named by\n"
      << "                      --ops as DIMACS, with a header mapping the\n"
      << "                      input/output bits to variables, and exit\n"
      << "  --dump-width W      at this width (default 64)\n"
      << "  --cnf HOW           how to generate the CNF --bcp-check and\n"
      << "                      --consistency propagate over: simple,\n"
      << "                      very-low, low, medium, high, very-high,\n"
      << "                      new-very-low, new-low, new-medium, gia-low,\n"
      << "                      gia-high, gia-very-high. Different encodings\n"
      << "                      of the same circuit propagate differently\n"
      << "  --bb.add-v1 0|1     UserDefinedFlags::adder_variant: 1 the\n"
      << "                      shared-half-adder full adder (default), 0\n"
      << "                      the majority-carry form\n"
      << "  --bb.add-v2 0|1     UserDefinedFlags::bvplus_variant: 1 pairwise\n"
      << "                      ripple chains (default), 0 the addition\n"
      << "                      network\n"
      << "  --no-shift-bias     draw shift amounts uniformly, instead of\n"
      << "                      half of them from [0, width)\n"
      << "  --seed N            random seed (default 42)\n"
      << "  --html FILE         write an HTML report\n"
      << "  --csv FILE          write the rows as CSV\n"
      << "  --list              list the operations and exit\n"
      << "  --verbose           report progress on stderr\n";
}

void list()
{
  std::cout << "operation      cbitp interval valueset\n";
  for (const OpSpec& op : allOps())
  {
    std::cout.width(15);
    std::cout << std::left << op.name;
    std::cout << (supports(Domain::Cbitp, op) ? "yes   " : "-     ")
              << (supports(Domain::Interval, op) ? "yes      " : "-        ")
              << (supports(Domain::ValueSet, op) ? "yes" : "-") << "\n";
  }
}

} // namespace

int main(int argc, char** argv)
{
  Config cfg;
  cfg.domains = {Domain::Cbitp, Domain::Interval, Domain::ValueSet};

  for (int i = 1; i < argc; i++)
  {
    const string arg = argv[i];
    const bool hasValue = (i + 1 < argc);
    const string value = hasValue ? argv[i + 1] : "";

    if (arg == "--help" || arg == "-h")
    {
      usage();
      return 0;
    }
    else if (arg == "--list")
    {
      list();
      return 0;
    }
    else if (arg == "--no-precision")
      cfg.precision = false;
    else if (arg == "--no-shift-bias")
      cfg.shiftBias = false;
    else if (arg == "--verbose" || arg == "-v")
      cfg.verbose = true;
    else if (!hasValue)
    {
      std::cerr << "propagator_bench: " << arg << " needs a value\n";
      return 1;
    }
    else if (arg == "--domains")
    {
      cfg.domains.clear();
      for (const string& d : split(value))
      {
        Domain parsed;
        if (!parseDomain(d, parsed))
        {
          std::cerr << "propagator_bench: unknown domain " << d << "\n";
          return 1;
        }
        cfg.domains.push_back(parsed);
      }
      i++;
    }
    else if (arg == "--ops")
    {
      cfg.ops = split(value);
      for (const string& o : cfg.ops)
        if (findOp(o) == NULL)
        {
          std::cerr << "propagator_bench: unknown operation " << o
                    << " (--list shows them)\n";
          return 1;
        }
      i++;
    }
    else if (arg == "--directions")
    {
      cfg.directions.clear();
      for (const string& d : split(value))
      {
        Direction parsed;
        if (!parseDirection(d, parsed))
        {
          std::cerr << "propagator_bench: unknown direction " << d << "\n";
          return 1;
        }
        cfg.directions.push_back(parsed);
      }
      i++;
    }
    else if (arg == "--widths") { cfg.widths = splitNumbers(value); i++; }
    else if (arg == "--probs") { cfg.probs = splitNumbers(value); i++; }
    else if (arg == "--set-sizes") { cfg.setSizes = splitNumbers(value); i++; }
    else if (arg == "--arity") { cfg.arity = atoi(value.c_str()); i++; }
    else if (arg == "--iterations") { cfg.iterations = atoi(value.c_str()); i++; }
    else if (arg == "--budget") { cfg.budgetSeconds = atof(value.c_str()); i++; }
    else if (arg == "--repeats") { cfg.repeats = atoi(value.c_str()); i++; }
    else if (arg == "--precision-width")
    { cfg.precisionWidth = atoi(value.c_str()); i++; }
    else if (arg == "--sat-check") { cfg.satCases = atoi(value.c_str()); i++; }
    else if (arg == "--sat-budget")
    { cfg.satBudgetSeconds = atof(value.c_str()); i++; }
    else if (arg == "--bcp-check") { cfg.bcpCases = atoi(value.c_str()); i++; }
    else if (arg == "--bcp-budget")
    { cfg.bcpBudgetSeconds = atof(value.c_str()); i++; }
    else if (arg == "--bcp-exhaustive")
    { cfg.bcpExhaustiveWidth = atoi(value.c_str()); i++; }
    else if (arg == "--consistency")
    { cfg.consistencyWidth = atoi(value.c_str()); i++; }
    else if (arg == "--dump-cnf") { cfg.dumpCnf = value; i++; }
    else if (arg == "--dump-width")
    { cfg.dumpWidth = atoi(value.c_str()); i++; }
    else if (arg == "--consistency-cap")
    { cfg.consistencyCap = strtoull(value.c_str(), NULL, 10); i++; }
    else if (arg == "--pc-samples")
    { cfg.pcSamples = strtoull(value.c_str(), NULL, 10); i++; }
    else if (arg == "--bb.add-v1")
    { cfg.adderVariant = atoi(value.c_str()); i++; }
    else if (arg == "--bb.add-v2")
    { cfg.bvplusVariant = atoi(value.c_str()); i++; }
    else if (arg == "--cnf") { cfg.cnf = value; i++; }
    else if (arg == "--seed") { cfg.seed = atoi(value.c_str()); i++; }
    else if (arg == "--html") { cfg.html = value; i++; }
    else if (arg == "--csv") { cfg.csv = value; i++; }
    else
    {
      std::cerr << "propagator_bench: unknown option " << arg << "\n";
      usage();
      return 1;
    }
  }

  if (cfg.iterations == 0 || cfg.repeats == 0)
  {
    std::cerr << "propagator_bench: --iterations and --repeats must be "
                 "positive\n";
    return 1;
  }

  if ((cfg.bcpCases > 0 || cfg.bcpExhaustiveWidth > 0 ||
       cfg.consistencyWidth > 0) &&
      !bcpAvailable())
  {
    // Refuse rather than silently report nothing: the whole point of the
    // option is the comparison it makes.
    std::cerr << "propagator_bench: --bcp-check/--bcp-exhaustive/--consistency "
                 "need a build with CryptoMiniSat (configure with "
                 "-DNOCRYPTOMINISAT=OFF)\n";
    return 1;
  }

  stp::STPMgr* mgr = new stp::STPMgr();
  stp::Cpp_interface interface(*mgr, mgr->defaultNodeFactory);
  interface.startup();
  stp::GlobalParserBM = mgr;

  if (!cfg.cnf.empty())
  {
    typedef stp::UserDefinedFlags UF;
    UF& uf = mgr->UserFlags;
    if (cfg.cnf == "simple")
      uf.simple_cnf = true;
    else if (cfg.cnf == "very-low")
      uf.cnf_effort = UF::CNF_EFFORT_VERY_LOW;
    else if (cfg.cnf == "low")
      uf.cnf_effort = UF::CNF_EFFORT_LOW;
    else if (cfg.cnf == "medium")
      uf.cnf_effort = UF::CNF_EFFORT_MEDIUM;
    else if (cfg.cnf == "high")
      uf.cnf_effort = UF::CNF_EFFORT_HIGH;
    else if (cfg.cnf == "very-high")
      uf.cnf_effort = UF::CNF_EFFORT_VERY_HIGH;
    else if (cfg.cnf == "new-very-low")
      uf.cnf_effort = UF::CNF_EFFORT_NEW_VERY_LOW;
    else if (cfg.cnf == "new-low")
      uf.cnf_effort = UF::CNF_EFFORT_NEW_LOW;
    else if (cfg.cnf == "new-medium")
      uf.cnf_effort = UF::CNF_EFFORT_NEW_MEDIUM;
    else if (cfg.cnf == "gia-low")
      uf.cnf_effort = UF::CNF_EFFORT_GIA_LOW;
    else if (cfg.cnf == "gia-high")
      uf.cnf_effort = UF::CNF_EFFORT_GIA_HIGH;
    else if (cfg.cnf == "gia-very-high")
      uf.cnf_effort = UF::CNF_EFFORT_GIA_VERY_HIGH;
    else
    {
      std::cerr << "propagator_bench: unknown --cnf value '" << cfg.cnf
                << "' (simple, very-low, low, medium, high, very-high, "
                   "new-very-low, new-low, new-medium, gia-low, gia-high, "
                   "gia-very-high)\n";
      return 1;
    }
  }

  if (cfg.adderVariant >= 0)
    mgr->UserFlags.adder_variant = cfg.adderVariant != 0;
  if (cfg.bvplusVariant >= 0)
    mgr->UserFlags.bvplus_variant = cfg.bvplusVariant != 0;

  if (!cfg.dumpCnf.empty())
  {
    if (cfg.ops.size() != 1 || !bcpAvailable())
    {
      std::cerr << "propagator_bench: --dump-cnf needs exactly one --ops "
                   "operation and a CryptoMiniSat build\n";
      return 1;
    }
    if (!dumpEncoding(mgr, *findOp(cfg.ops[0]), cfg, cfg.dumpCnf))
    {
      std::cerr << "propagator_bench: could not encode " << cfg.ops[0]
                << " at width " << cfg.dumpWidth << "\n";
      return 1;
    }
    std::cout << "wrote " << cfg.dumpCnf << std::endl;
    return 0;
  }

  vector<Row> rows;
  for (Domain d : cfg.domains)
  {
    switch (d)
    {
      case Domain::Cbitp: runCbitp(mgr, cfg, rows); break;
      case Domain::Interval: runInterval(mgr, cfg, rows); break;
      case Domain::ValueSet: runValueSet(mgr, cfg, rows); break;
    }
  }

  printText(cfg, rows);
  if (!cfg.csv.empty())
    writeCsv(cfg, rows, cfg.csv);
  if (!cfg.html.empty())
    writeHtml(cfg, rows, cfg.html);

  return 0;
}
