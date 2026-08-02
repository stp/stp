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

  if (cfg.bcpCases > 0 && !bcpAvailable())
  {
    // Refuse rather than silently report nothing: the whole point of the
    // option is the comparison it makes.
    std::cerr << "propagator_bench: --bcp-check needs a build with "
                 "CryptoMiniSat (configure with -DNOCRYPTOMINISAT=OFF)\n";
    return 1;
  }

  stp::STPMgr* mgr = new stp::STPMgr();
  stp::Cpp_interface interface(*mgr, mgr->defaultNodeFactory);
  interface.startup();
  stp::GlobalParserBM = mgr;

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
