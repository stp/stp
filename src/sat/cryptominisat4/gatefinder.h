/*
 * CryptoMiniSat
 *
 * Copyright (c) 2009-2013, Mate Soos. All rights reserved.
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.0 of the License.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston,
 * MA 02110-1301  USA
 */

#ifndef _GATEFINDER_H_
#define _GATEFINDER_H_

#include "solvertypes.h"
#include "cset.h"
#include <set>
#include "watcharray.h"
#include <array>

namespace CMSat {

class Solver;
class Simplifier;
using std::set;

class OrGate {
    public:
        OrGate(const Lit& _eqLit, Lit _lit1, Lit _lit2, const bool _red) :
            lit1(_lit1)
            , lit2(_lit2)
            , eqLit(_eqLit)
            , red(_red)
        {
            if (lit1 > lit2)
                std::swap(lit1, lit2);
        }

        bool operator==(const OrGate& other) const
        {
            return
                eqLit == other.eqLit
                && lit1 == other.lit1
                && lit2 == other.lit2
                ;
        }
        std::array<Lit, 2> getLits() const
        {
            return std::array<Lit, 2>{{lit1, lit2}};
        }

        //LHS
        Lit lit1;
        Lit lit2;

        //RHS
        Lit eqLit;

        //Data about gate
        bool red;
};

struct GateCompareForEq
{
    bool operator()(const OrGate& a, const OrGate& b) const
    {
        if (a.lit1 != b.lit1) {
            return (a.lit1 < b.lit1);
        }

        if (a.lit2 != b.lit2) {
            return (a.lit2 < b.lit2);
        }
        return (a.eqLit < b.eqLit);
    }
};

inline std::ostream& operator<<(std::ostream& os, const OrGate& gate)
{
    os
    << " gate "
    << " lits: " << gate.lit1 << ", " << gate.lit2
    << " eqLit: " << gate.eqLit
    << " learnt " << gate.red
    ;
    return os;
}

class GateFinder
{
public:
    GateFinder(Simplifier *subsumer, Solver *control);

    void new_var(const Var orig_outer);
    void new_vars(const size_t n);
    void saveVarMem();
    bool doAll();

    //Getter functions
    void printGateStats() const;
    void printDot(); ///<Print Graphviz DOT file describing the gates

    //Stats
    struct Stats
    {
        void clear()
        {
            Stats tmp;
            *this = tmp;
        }

        double totalTime() const
        {
            return findGateTime + orBasedTime + varReplaceTime
                + andBasedTime + erTime;
        }
        Stats& operator+=(const Stats& other);
        void print(const size_t nVars) const;
        void printShort() const;

        //Time
        double findGateTime = 0.0;
        uint32_t find_gate_timeout = 0;
        double orBasedTime = 0.0;
        uint32_t or_based_timeout = 0;
        double varReplaceTime = 0.0;
        double andBasedTime = 0.0;
        uint32_t and_based_timeout = 0;
        double erTime = 0.0;

        //OR-gate
        uint64_t orGateUseful = 0;
        uint64_t numLongCls = 0;
        uint64_t numLongClsLits = 0;
        int64_t  litsRem = 0;

        //Var-replace
        uint64_t varReplaced = 0;

        //And-gate
        uint64_t andGateUseful = 0;
        uint64_t clauseSizeRem = 0;

        //ER
        uint64_t numERVars = 0;

        //Gates
        uint64_t learntGatesSize = 0;
        uint64_t numRed = 0;
        uint64_t irredGatesSize = 0;
        uint64_t numIrred = 0;
    };

    const Stats& getStats() const;

private:
    //Setup
    void clearIndexes();
    void link_in_gate(const OrGate& gate);
    void add_gate_if_not_already_inside(Lit eqLit, Lit lit1, Lit lit2);
    void find_or_gates_in_sweep_mode(Lit lit);

    //High-level functions
    bool remove_clauses_with_all_or_gates();
    bool shorten_with_all_or_gates();

    //Finding
    void find_or_gates_and_update_stats();
    void find_or_gates();
    void findOrGate(
        const Lit eqLit
        , const Lit lit1
        , const Lit lit2
    );

    bool all_simplifications_with_gates();
    vector<ClOffset> subs; //to reduce overhead of allocation
    bool shortenWithOrGate(const OrGate& gate);
    size_t findEqOrGates();

    //And gate treatment
    bool remove_clauses_using_and_gate(
        const OrGate& gate
        , const bool reallyRemove
        , const bool only_irred
        , uint32_t& reduction
    );

    cl_abst_type  calc_sorted_occ_and_set_seen2(
        const OrGate& gate
        , uint32_t& maxSize
        , uint32_t& minSize
        , const bool only_irred
    );
    void set_seen2_and_abstraction(
        const Clause& cl
        , cl_abst_type& abstraction
    );
    bool check_seen_and_gate_against_cl(
        const Clause& this_cl
        , const OrGate& gate
    );

    void treatAndGateClause(
        const ClOffset other_cl_offset
        , const OrGate& gate
        , const ClOffset this_cl_offset
    );
    cl_abst_type calc_abst_and_set_seen(
       const Clause& cl
        , const OrGate& gate
    );
    ClOffset find_pair_for_and_gate_reduction(
        const Watched& ws
        , const size_t minSize
        , const size_t maxSize
        , const cl_abst_type abstraction
        , const OrGate& gate
        , const bool only_irred
    );

    ClOffset findAndGateOtherCl(
        const vector<ClOffset>& this_sizeSortedOcc
        , const Lit lit
        , const cl_abst_type abst2
        , const bool gate_is_red
        , const bool only_irred
    );
    bool findAndGateOtherCl_tri(
       watch_subarray_const ws_list
       , const bool gate_is_red
       , const bool only_irred
       , Watched& ret
    );
    bool find_pair_for_and_gate_reduction_tri(
        const Watched& ws
        , const OrGate& gate
        , const bool only_irred
        , Watched& found_pair
    );
    bool remove_clauses_using_and_gate_tri(
       const OrGate& gate
        , const bool really_remove
        , const bool only_irred
        , uint32_t& reduction
    );
    void set_seen2_tri(
       const OrGate& gate
        , const bool only_irred
    );
    bool check_seen_and_gate_against_lit(
        const Lit lit
        , const OrGate& gate
    );

    ///temporary for and-gate treatment. Cleared at every treatAndGate() call
    vector<vector<ClOffset> > sizeSortedOcc;

    //Indexes, gate data
    vector<OrGate> orGates; //List of OR gates
    vector<vector<uint32_t> > gateOcc; //LHS of every NON-LEARNT gate is in this occur list (a = b V c, so 'a' is LHS)
    vector<vector<uint32_t> > gateOccEq; //RHS of every gate is in this occur list (a = b V c, so 'b' and 'c' are LHS)

    //For temporaries
    vector<size_t> seen2Set; //Bits that have been set in seen2, and later need to be cleared
    set<ClOffset> clToUnlink;
    struct TriToUnlink
    {
        TriToUnlink(Lit _lit2, Lit _lit3, bool _red) :
            lit2(_lit2)
            , lit3(_lit3)
            , red(_red)
        {}

        const Lit lit2;
        const Lit lit3;
        const bool red;

        bool operator<(const TriToUnlink& other) const
        {
            if (lit2 != other.lit2)
                return lit2 < other.lit2;
            if (lit3 != other.lit3)
                return lit3 < other.lit3;
            return red < other.red;
        }
    };
    set<TriToUnlink> tri_to_unlink;

    //Graph
    void printDot2(); ///<Print Graphviz DOT file describing the gates

    //Stats
    Stats runStats;
    Stats globalStats;

    //Limits
    int64_t  numMaxGateFinder;
    int64_t  numMaxShortenWithGates;
    int64_t  numMaxClRemWithGates;

    //long-term stats
    uint64_t numDotPrinted;

    //Main data
    Simplifier *simplifier;
    Solver *solver;
    vector<uint16_t>& seen;
    vector<uint16_t>& seen2;
    vector<Lit>& toClear;
};

inline const GateFinder::Stats& GateFinder::getStats() const
{
    return globalStats;
}

} //end namespace

#endif //_GATEFINDER_H_
