#include "FloatSimplex.h"

#include <cmath>
#include <cstdio>
#include <optional>
#include <stdexcept>
#include <string>

namespace
{

using stp::lra::ExactLraResourceObserver;
using stp::lra::FloatSimplex;
using stp::lra::Relation;
using stp::lra::StopReason;

struct PermissiveObserver final : ExactLraResourceObserver
{
  StopReason pollBeforePivot() noexcept override
  {
    return StopReason::Continue;
  }
  void accountPivot(bool) noexcept override {}
};

void require(bool condition, const char* what)
{
  if (!condition)
    throw std::runtime_error(what);
}

/* rows: r1 = x + y ; r2 = x ; r3 = y, with atoms
 *   a_sum_le3: r1 <= 3, a_sum_ge5: r1 >= 5,
 *   a_x_ge2: r2 >= 2, a_y_ge2: r3 >= 2, a_x_le5: r2 <= 5. */
struct Fixture final
{
  FloatSimplex simplex;
  FloatSimplex::Atom sum_le3;
  FloatSimplex::Atom sum_ge5;
  FloatSimplex::Atom x_ge2;
  FloatSimplex::Atom y_ge2;
  FloatSimplex::Atom x_le5;

  Fixture()
  {
    const FloatSimplex::Var x = simplex.addColumn();
    const FloatSimplex::Var y = simplex.addColumn();
    const FloatSimplex::Term sum_terms[] = {{x, 1.0}, {y, 1.0}};
    const FloatSimplex::Var r1 = simplex.addRow(sum_terms, sum_terms + 2);
    const FloatSimplex::Term x_terms[] = {{x, 1.0}};
    const FloatSimplex::Var r2 = simplex.addRow(x_terms, x_terms + 1);
    const FloatSimplex::Term y_terms[] = {{y, 1.0}};
    const FloatSimplex::Var r3 = simplex.addRow(y_terms, y_terms + 1);
    sum_le3 = simplex.addAtom(r1, Relation::LessEqual, 3.0);
    sum_ge5 = simplex.addAtom(r1, Relation::GreaterEqual, 5.0);
    x_ge2 = simplex.addAtom(r2, Relation::GreaterEqual, 2.0);
    y_ge2 = simplex.addAtom(r3, Relation::GreaterEqual, 2.0);
    x_le5 = simplex.addAtom(r2, Relation::LessEqual, 5.0);
    require(simplex.finalize(), "finalize");
  }
};

void exerciseOneMode(bool factorized)
{
  PermissiveObserver observer;
  const char* const mode = factorized ? "factorized" : "substitution";
  const std::string tag(mode);

  {
    /* x + y <= 3 with x >= 2 and y >= 2 is infeasible via the row; the
     * certificate must name all three bounds. */
    Fixture fixture;
    if (factorized)
      fixture.simplex.switchToFactorized();
    require(fixture.simplex.assertAtom(fixture.sum_le3, true) ==
                FloatSimplex::AssertOutcome::Ok,
            "sum<=3 accepted");
    require(fixture.simplex.assertAtom(fixture.x_ge2, true) ==
                FloatSimplex::AssertOutcome::Ok,
            "x>=2 accepted");
    require(fixture.simplex.assertAtom(fixture.y_ge2, true) ==
                FloatSimplex::AssertOutcome::Ok,
            "y>=2 accepted");
    require(fixture.simplex.check(observer) ==
                FloatSimplex::Verdict::InfeasibleCandidate,
            (tag + ": row infeasibility detected").c_str());
    const FloatSimplex::Certificate& certificate =
        fixture.simplex.lastCertificate();
    require(certificate.valid, (tag + ": certificate valid").c_str());
    require(certificate.items.size() == 3,
            (tag + ": certificate has three bounds").c_str());
    for (const FloatSimplex::CertificateItem& item : certificate.items)
      require(item.weight > 0.0,
              (tag + ": certificate weights positive").c_str());
    /* Undoing the last assert restores feasibility. */
    fixture.simplex.undoTo(2);
    require(fixture.simplex.check(observer) ==
                FloatSimplex::Verdict::Feasible,
            (tag + ": feasible after undo").c_str());
  }

  {
    /* Feasible system; the assignment must satisfy the asserted bounds.
     * x + y >= 5 forces a structural variable into the basis in the
     * factorized representation (the kernel grows). */
    Fixture fixture;
    if (factorized)
      fixture.simplex.switchToFactorized();
    require(fixture.simplex.assertAtom(fixture.sum_ge5, true) ==
                FloatSimplex::AssertOutcome::Ok,
            "sum>=5 accepted");
    require(fixture.simplex.assertAtom(fixture.x_le5, true) ==
                FloatSimplex::AssertOutcome::Ok,
            "x<=5 accepted");
    require(fixture.simplex.check(observer) ==
                FloatSimplex::Verdict::Feasible,
            (tag + ": feasible with sum>=5").c_str());
    const FloatSimplex::DVal x_value = fixture.simplex.assignmentOf(0);
    const FloatSimplex::DVal y_value = fixture.simplex.assignmentOf(1);
    require(x_value.value + y_value.value >= 5.0 - 1.0e-6,
            (tag + ": assignment satisfies sum>=5").c_str());
    require(x_value.value <= 5.0 + 1.0e-6,
            (tag + ": assignment satisfies x<=5").c_str());
  }

  {
    /* Starting the assignment over keeps the feasibility question: the
     * bounds and the trail are what the answer depends on, and
     * rebuildAssignment leaves both alone.  Both verdicts have to
     * survive it, since the infinitesimal guard can fire in the middle
     * of any check. */
    Fixture fixture;
    if (factorized)
      fixture.simplex.switchToFactorized();
    require(fixture.simplex.assertAtom(fixture.sum_ge5, true) ==
                FloatSimplex::AssertOutcome::Ok,
            "sum>=5 accepted");
    require(fixture.simplex.assertAtom(fixture.x_le5, true) ==
                FloatSimplex::AssertOutcome::Ok,
            "x<=5 accepted");
    require(fixture.simplex.check(observer) ==
                FloatSimplex::Verdict::Feasible,
            (tag + ": feasible before rebuild").c_str());
    const std::size_t trail_before = fixture.simplex.trail().size();
    fixture.simplex.rebuildAssignment();
    require(fixture.simplex.assignmentRebuilds() == 1,
            (tag + ": rebuild counted").c_str());
    require(fixture.simplex.trail().size() == trail_before,
            (tag + ": rebuild leaves the trail alone").c_str());
    require(fixture.simplex.check(observer) ==
                FloatSimplex::Verdict::Feasible,
            (tag + ": feasible after rebuild").c_str());
    const FloatSimplex::DVal x_after = fixture.simplex.assignmentOf(0);
    const FloatSimplex::DVal y_after = fixture.simplex.assignmentOf(1);
    require(x_after.value + y_after.value >= 5.0 - 1.0e-6,
            (tag + ": rebuilt assignment satisfies sum>=5").c_str());
    require(x_after.value <= 5.0 + 1.0e-6,
            (tag + ": rebuilt assignment satisfies x<=5").c_str());
  }

  {
    /* And the infeasible direction: a conflict the check has to find,
     * still found and still certified after the assignment has been
     * thrown away. */
    Fixture fixture;
    if (factorized)
      fixture.simplex.switchToFactorized();
    require(fixture.simplex.assertAtom(fixture.sum_le3, true) ==
                FloatSimplex::AssertOutcome::Ok,
            "sum<=3 accepted");
    require(fixture.simplex.assertAtom(fixture.x_ge2, true) ==
                FloatSimplex::AssertOutcome::Ok,
            "x>=2 accepted");
    require(fixture.simplex.assertAtom(fixture.y_ge2, true) ==
                FloatSimplex::AssertOutcome::Ok,
            "y>=2 accepted");
    fixture.simplex.rebuildAssignment();
    require(fixture.simplex.check(observer) ==
                FloatSimplex::Verdict::InfeasibleCandidate,
            (tag + ": infeasible after rebuild").c_str());
    const FloatSimplex::Certificate& rebuilt =
        fixture.simplex.lastCertificate();
    require(rebuilt.valid && rebuilt.items.size() == 3,
            (tag + ": certificate survives the rebuild").c_str());
  }

  {
    /* A direct bound clash on one row variable; the certificate is the
     * pair, in either representation. */
    Fixture fixture;
    if (factorized)
      fixture.simplex.switchToFactorized();
    require(fixture.simplex.assertAtom(fixture.x_le5, true) ==
                FloatSimplex::AssertOutcome::Ok,
            "x<=5 accepted");
    require(fixture.simplex.assertAtom(fixture.x_ge2, false) ==
                FloatSimplex::AssertOutcome::Ok,
            "not(x>=2) accepted");
    /* not(x>=2) installs x < 2; asserting x >= 2 now clashes. */
    require(fixture.simplex.assertAtom(fixture.x_ge2, true) ==
                FloatSimplex::AssertOutcome::LocalConflict,
            (tag + ": clash detected").c_str());
    const FloatSimplex::Certificate& certificate =
        fixture.simplex.lastCertificate();
    require(certificate.valid && certificate.items.size() == 2,
            (tag + ": clash certificate is the pair").c_str());
  }

  {
    /* Strict infeasibility carried by the delta components only:
     * x + y < 3 (strict) with x >= 1 and y >= 2. */
    FloatSimplex simplex;
    const FloatSimplex::Var x = simplex.addColumn();
    const FloatSimplex::Var y = simplex.addColumn();
    const FloatSimplex::Term sum_terms[] = {{x, 1.0}, {y, 1.0}};
    const FloatSimplex::Var r1 = simplex.addRow(sum_terms, sum_terms + 2);
    const FloatSimplex::Term x_terms[] = {{x, 1.0}};
    const FloatSimplex::Var r2 = simplex.addRow(x_terms, x_terms + 1);
    const FloatSimplex::Term y_terms[] = {{y, 1.0}};
    const FloatSimplex::Var r3 = simplex.addRow(y_terms, y_terms + 1);
    const FloatSimplex::Atom sum_lt3 =
        simplex.addAtom(r1, Relation::Less, 3.0);
    const FloatSimplex::Atom x_ge1 =
        simplex.addAtom(r2, Relation::GreaterEqual, 1.0);
    const FloatSimplex::Atom y_ge2 =
        simplex.addAtom(r3, Relation::GreaterEqual, 2.0);
    require(simplex.finalize(), "strict finalize");
    if (factorized)
      simplex.switchToFactorized();
    require(simplex.assertAtom(sum_lt3, true) ==
                FloatSimplex::AssertOutcome::Ok,
            "sum<3 accepted");
    require(simplex.assertAtom(x_ge1, true) ==
                FloatSimplex::AssertOutcome::Ok,
            "x>=1 accepted");
    require(simplex.assertAtom(y_ge2, true) ==
                FloatSimplex::AssertOutcome::Ok,
            "y>=2 accepted");
    require(simplex.check(observer) ==
                FloatSimplex::Verdict::InfeasibleCandidate,
            (tag + ": strict infeasibility detected").c_str());
  }
}

void testEarlyConflict()
{
  PermissiveObserver observer;
  for (bool enabled : {false, true})
  for (bool strict : {false, true})
  {
    FloatSimplex s;
    s.setEarlyConflictDetection(enabled);
    auto x = s.addColumn(), y = s.addColumn(), z = s.addColumn(), w = s.addColumn();
    auto identity = [&](FloatSimplex::Var v) {
      FloatSimplex::Term term{v, 1.0};
      return s.addRow(&term, &term + 1);
    };
    auto rx = identity(x), ry = identity(y), rz = identity(z), rw = identity(w);
    FloatSimplex::Term terms[] = {{x, 1.0}, {y, 1.0}, {z, -1.0}};
    auto sum = s.addRow(terms, terms + 3);
    auto ax = s.addAtom(rx, Relation::GreaterEqual, 1.0);
    auto ay = s.addAtom(ry, Relation::GreaterEqual, 1.0);
    auto az = s.addAtom(rz, Relation::LessEqual, -1.0);
    auto aw = s.addAtom(rw, Relation::GreaterEqual, 1.0);
    auto bad = s.addAtom(sum, strict ? Relation::Less : Relation::LessEqual,
                        strict ? 3.0 : 2.0);
    auto good = s.addAtom(sum, Relation::LessEqual, 4.0);
    require(s.finalize(), "early conflict finalize");
    for (auto atom : {ax, ay, az})
      require(s.assertAtom(atom, true) == FloatSimplex::AssertOutcome::Ok, "warm assert");
    require(s.check(observer) == FloatSimplex::Verdict::Feasible, "warm basis");
    auto before = s.pivots();
    s.assertAtom(bad, true);
    s.assertAtom(aw, true);
    require(s.check(observer) == FloatSimplex::Verdict::InfeasibleCandidate,
            "early row conflict");
    require(s.lastCertificate().valid && s.lastCertificate().items.size() == 4,
            "early certificate support");
    require(s.pivots() - before == (enabled ? 0U : 1U), "early detection saves pivot");
    require(s.earlyConflicts() == (enabled ? 1U : 0U), "early conflict counted");
    s.undoTo(3);
    s.assertAtom(good, true);
    require(s.check(observer) == FloatSimplex::Verdict::Feasible, "pop restores movement");
    s.restartBasis();
    require(s.check(observer) == FloatSimplex::Verdict::Feasible, "restart resets counters");
    s.switchToFactorized();
    require(s.check(observer) == FloatSimplex::Verdict::Feasible, "factorized transition");
  }
}

void testSoi()
{
  PermissiveObserver observer;
  for (bool enabled : {false, true})
  for (bool strict : {false, true})
  {
    FloatSimplex s;
    s.setSoi(enabled);
    s.setEarlyConflictDetection(true);
    auto x = s.addColumn(), a = s.addColumn(), b = s.addColumn(), c = s.addColumn();
    FloatSimplex::Term ta[] = {{x, 1.0}, {a, 1.0}};
    FloatSimplex::Term tb[] = {{x, 1.0}, {b, 1.0}};
    FloatSimplex::Term tc[] = {{x, 1.0}, {c, -1.0}};
    auto ra = s.addRow(ta, ta + 2), rb = s.addRow(tb, tb + 2), rc = s.addRow(tc, tc + 2);
    auto relation = strict ? Relation::Greater : Relation::GreaterEqual;
    auto aa = s.addAtom(ra, relation, strict ? 0.0 : 1.0);
    auto ab = s.addAtom(rb, relation, strict ? 0.0 : 1.0);
    auto ac = s.addAtom(rc, relation, strict ? 0.0 : 1.0);
    require(s.finalize(), "SOI finalize");
    for (auto atom : {aa, ab, ac})
      s.assertAtom(atom, true);
    require(s.check(observer) == FloatSimplex::Verdict::Feasible, "SOI hub feasible");
    require(s.pivots() == (enabled ? 1U : 3U), "SOI hub saves two pivots");
    require(s.soiSteps() == (enabled ? 1U : 0U), "SOI hub step counted");
    s.undoTo(0);
    s.restartBasis();
    require(s.check(observer) == FloatSimplex::Verdict::Feasible, "SOI restart feasible");
  }
  {
    FloatSimplex s;
    s.setSoi(true);
    auto x = s.addColumn(), a = s.addColumn(), b = s.addColumn(), c = s.addColumn();
    FloatSimplex::Term tx{x, 1.0};
    auto rx = s.addRow(&tx, &tx + 1);
    FloatSimplex::Term ta[] = {{x, 1.0}, {a, 1.0}};
    FloatSimplex::Term tb[] = {{x, 1.0}, {b, 1.0}};
    FloatSimplex::Term tc[] = {{x, 1.0}, {c, 1.0}};
    auto ra = s.addRow(ta, ta + 2), rb = s.addRow(tb, tb + 2), rc = s.addRow(tc, tc + 2);
    auto lo = s.addAtom(rx, Relation::GreaterEqual, 1.0);
    auto hi = s.addAtom(rx, Relation::LessEqual, 2.0);
    auto aa = s.addAtom(ra, Relation::GreaterEqual, 3.0);
    auto ab = s.addAtom(rb, Relation::GreaterEqual, 3.0);
    auto ac = s.addAtom(rc, Relation::GreaterEqual, 3.0);
    require(s.finalize(), "SOI bound flip finalize");
    s.assertAtom(lo, true);
    require(s.check(observer) == FloatSimplex::Verdict::Feasible, "SOI bound flip warmup");
    for (auto atom : {hi, aa, ab, ac})
      s.assertAtom(atom, true);
    require(s.check(observer) == FloatSimplex::Verdict::Feasible, "SOI bound flip feasible");
    require(s.soiBoundFlips() > 0, "SOI bound flip counted");
    s.undoTo(1);
    require(s.check(observer) == FloatSimplex::Verdict::Feasible, "SOI bound flip pop");
  }
}

void testPersistentExtension()
{
  PermissiveObserver observer;
  for (bool factorized : {false, true})
  for (bool soi : {false, true})
  {
    FloatSimplex s;
    s.setEarlyConflictDetection(true);
    s.setSoi(soi);
    auto x = s.addColumn();
    FloatSimplex::Term tx{x, 1.0};
    auto rx = s.addRow(&tx, &tx + 1);
    auto lo = s.addAtom(rx, Relation::GreaterEqual, 1.0);
    require(s.finalize(), "extension finalize");
    if (factorized)
      s.switchToFactorized();
    s.assertAtom(lo, true);
    require(s.check(observer) == FloatSimplex::Verdict::Feasible, "extension warm basis");
    auto pivots = s.pivots(), restarts = s.restarts();
    s.undoTo(0);
    auto z = s.addColumn(); // structural variable after a row variable
    FloatSimplex::Term terms[] = {{z, -4.0}, {x, 2.0}}; // deliberately unsorted
    auto sum = s.addRow(terms, terms + 2);
    FloatSimplex::Term tz{z, 1.0};
    auto rz = s.addRow(&tz, &tz + 1);
    auto zhi = s.addAtom(rz, Relation::LessEqual, 0.0);
    auto good = s.addAtom(sum, Relation::GreaterEqual, 2.0);
    auto bad = s.addAtom(sum, Relation::Less, 2.0);
    for (auto atom : {lo, zhi, good})
      s.assertAtom(atom, true);
    require(s.check(observer) == FloatSimplex::Verdict::Feasible, "extended scaled rows feasible");
    require(s.pivots() == pivots && s.restarts() == restarts,
            "appending preserves basis and assignment");
    s.undoTo(0);
    for (auto atom : {lo, zhi, bad})
      s.assertAtom(atom, true);
    require(s.check(observer) == FloatSimplex::Verdict::InfeasibleCandidate &&
            s.lastCertificate().valid, "extended strict conflict");
    s.undoTo(1);
    require(s.check(observer) == FloatSimplex::Verdict::Feasible, "extended conflict pop");
    s.restartBasis();
    require(s.check(observer) == FloatSimplex::Verdict::Feasible, "extended pristine restart");
  }
}

void testDecisionPolarity()
{
  for (bool factorized : {false, true})
  {
    Fixture f;
    auto& s = f.simplex;
    if (factorized)
      s.switchToFactorized();
    PermissiveObserver observer;
    s.assertAtom(f.x_ge2, true);
    s.assertAtom(f.y_ge2, true);
    require(s.check(observer) == FloatSimplex::Verdict::Feasible, "polarity feasible assignment");
    auto pivots = s.pivots();
    require(s.preferredPolarity(f.sum_le3) == std::optional<bool>{false}, "false float polarity");
    require(s.preferredPolarity(f.x_le5) == std::optional<bool>{true}, "true float polarity");
    require(!s.preferredPolarity(f.x_ge2), "float boundary declines advice");
    require(!s.preferredPolarity(FloatSimplex::kNoAtom), "invalid float atom declines advice");
    require(s.pivots() == pivots, "float advice does not pivot");
    s.undoTo(0);
    s.restartBasis();
    s.assertAtom(f.x_ge2, true);
    s.assertAtom(f.y_ge2, true);
    require(s.check(observer) == FloatSimplex::Verdict::Feasible &&
            s.preferredPolarity(f.sum_le3) == std::optional<bool>{false},
            "polarity after restart and recheck");
  }
  FloatSimplex s;
  auto x = s.addColumn();
  FloatSimplex::Term t{x, 2.0};
  auto row = s.addRow(&t, &t + 1);
  auto strict = s.addAtom(row, Relation::Greater, 0.0);
  auto near = s.addAtom(row, Relation::LessEqual, 1e-12);
  require(s.finalize(), "strict advice build");
  s.assertAtom(strict, true);
  PermissiveObserver observer;
  require(s.check(observer) == FloatSimplex::Verdict::Feasible, "strict advice check");
  require(!s.preferredPolarity(strict) && !s.preferredPolarity(near),
          "float advice abstains on epsilon-only and near-boundary separations");
}

void testDormantRows()
{
  PermissiveObserver observer;
  {
    /* Every row starts dormant; a first bound wakes exactly its row; the
     * verdicts and the certificate are what the live tableau gives. */
    FloatSimplex s;
    s.setDormantRows(true);
    const FloatSimplex::Var x = s.addColumn();
    const FloatSimplex::Var y = s.addColumn();
    const FloatSimplex::Term sum_terms[] = {{x, 1.0}, {y, 1.0}};
    const FloatSimplex::Var r1 = s.addRow(sum_terms, sum_terms + 2);
    const FloatSimplex::Term x_terms[] = {{x, 1.0}};
    const FloatSimplex::Var r2 = s.addRow(x_terms, x_terms + 1);
    const FloatSimplex::Term y_terms[] = {{y, 1.0}};
    const FloatSimplex::Var r3 = s.addRow(y_terms, y_terms + 1);
    auto sum_le3 = s.addAtom(r1, Relation::LessEqual, 3.0);
    auto x_ge2 = s.addAtom(r2, Relation::GreaterEqual, 2.0);
    auto y_ge2 = s.addAtom(r3, Relation::GreaterEqual, 2.0);
    require(s.finalize(), "dormant finalize");
    require(s.dormantRows(), "dormancy recorded");
    require(s.dormantRowCount() == 3, "all rows dormant after finalize");
    require(s.check(observer) == FloatSimplex::Verdict::Feasible,
            "empty dormant tableau feasible");
    require(s.pivots() == 0, "no pivots with nothing bounded");

    require(s.assertAtom(x_ge2, true) == FloatSimplex::AssertOutcome::Ok, "x>=2");
    require(s.rowActivations() == 1 && s.dormantRowCount() == 2,
            "first bound activates exactly its row");
    require(s.check(observer) == FloatSimplex::Verdict::Feasible, "x>=2 feasible");
    /* r1 = x + y is still dormant: its value is evaluated on demand. */
    const FloatSimplex::DVal sum = s.assignmentOf(r1);
    const FloatSimplex::DVal xv = s.assignmentOf(x);
    const FloatSimplex::DVal yv = s.assignmentOf(y);
    require(std::fabs(sum.value - (xv.value + yv.value)) < 1e-9,
            "dormant basic evaluated from its row");
    require(s.dormantEvaluations() >= 1, "evaluation counted");
    /* Advice for an atom on a dormant row reads the same evaluation:
     * x + y = 2 against <= 3 favours true. */
    require(s.preferredPolarity(sum_le3) == std::optional<bool>{true},
            "advice on a dormant row's atom");

    require(s.assertAtom(sum_le3, true) == FloatSimplex::AssertOutcome::Ok, "sum<=3");
    require(s.assertAtom(y_ge2, true) == FloatSimplex::AssertOutcome::Ok, "y>=2");
    require(s.dormantRowCount() == 0 && s.rowActivations() == 3,
            "all rows active once all bounded");
    require(s.check(observer) == FloatSimplex::Verdict::InfeasibleCandidate,
            "dormant: row infeasibility detected");
    const FloatSimplex::Certificate& certificate = s.lastCertificate();
    require(certificate.valid && certificate.items.size() == 3,
            "dormant: certificate names all three bounds");
    /* Rows stay live across undo. */
    s.undoTo(1);
    require(s.dormantRowCount() == 0, "activated rows stay live on undo");
    require(s.check(observer) == FloatSimplex::Verdict::Feasible,
            "dormant: feasible after undo");
    /* A basis restart re-dormants what is unbounded and keeps what is. */
    s.restartBasis();
    require(s.dormantRowCount() == 2, "restart re-dormants unbounded rows");
    require(s.check(observer) == FloatSimplex::Verdict::Feasible,
            "dormant: feasible after restart");
    s.assertAtom(sum_le3, true);
    s.assertAtom(y_ge2, true);
    require(s.check(observer) == FloatSimplex::Verdict::InfeasibleCandidate,
            "dormant: infeasible again after restart");
  }
  {
    /* Activation after pivots: a dormant row whose terms have entered the
     * basis is normalised on the way in and judged correctly.
     *   r1 = x - y,  r2 = x,  r3 = x + y (dormant until last).
     * Asserting r1 >= 1 and r2 <= 0 needs a pivot that brings a
     * structural into the basis before r3 wakes up. */
    FloatSimplex s;
    s.setDormantRows(true);
    const FloatSimplex::Var x = s.addColumn();
    const FloatSimplex::Var y = s.addColumn();
    const FloatSimplex::Term t1[] = {{x, 1.0}, {y, -1.0}};
    const FloatSimplex::Term t2[] = {{x, 1.0}};
    const FloatSimplex::Term t3[] = {{x, 1.0}, {y, 1.0}};
    auto r1 = s.addRow(t1, t1 + 2);
    auto r2 = s.addRow(t2, t2 + 1);
    auto r3 = s.addRow(t3, t3 + 2);
    auto a1 = s.addAtom(r1, Relation::GreaterEqual, 1.0);
    auto a2 = s.addAtom(r2, Relation::LessEqual, 0.0);
    auto a3_hi = s.addAtom(r3, Relation::LessEqual, -1.0);
    auto a3_lo = s.addAtom(r3, Relation::GreaterEqual, 5.0);
    require(s.finalize(), "pivot fixture finalize");
    s.assertAtom(a1, true);
    s.assertAtom(a2, true);
    require(s.check(observer) == FloatSimplex::Verdict::Feasible, "x - y >= 1, x <= 0 feasible");
    require(s.pivots() >= 1, "a pivot happened while r3 slept");
    require(s.dormantRowCount() == 1, "r3 still dormant through the pivot");
    const std::size_t mark = s.mark();
    /* x + y <= -1 is consistent (x = 0, y = -1 works). */
    s.assertAtom(a3_hi, true);
    require(s.rowActivations() == 3, "r3 activated by its first bound");
    require(s.check(observer) == FloatSimplex::Verdict::Feasible,
            "normalised row judged feasible");
    const FloatSimplex::DVal xv = s.assignmentOf(x), yv = s.assignmentOf(y);
    require(xv.value - yv.value >= 1.0 - 1e-6 && xv.value <= 1e-6 &&
                xv.value + yv.value <= -1.0 + 1e-6,
            "assignment satisfies all three after activation");
    s.undoTo(mark);
    /* x + y >= 5 with x <= 0 and x - y >= 1 is infeasible. */
    s.assertAtom(a3_lo, true);
    require(s.check(observer) == FloatSimplex::Verdict::InfeasibleCandidate,
            "normalised row conflict found");
    require(s.lastCertificate().valid, "normalised row conflict certified");
  }
  {
    /* Appended rows start dormant too, and factorized mode ignores the
     * discipline entirely. */
    Fixture f;
    auto& s = f.simplex;
    require(!s.dormantRows() && s.dormantRowCount() == 0, "off by default");
    s.setDormantRows(true);
    require(s.dormantRowCount() == 3, "enable after finalize on an empty trail");
    s.assertAtom(f.x_ge2, true);
    bool threw = false;
    try { s.setDormantRows(false); } catch (const std::exception&) { threw = true; }
    require(threw, "toggling with bounds asserted is refused");
    s.undoTo(0);
    auto z = s.addColumn();
    FloatSimplex::Term tz{z, 1.0};
    auto rz = s.addRow(&tz, &tz + 1);
    require(s.dormantRowCount() == 3, "appended row starts dormant");
    auto zlo = s.addAtom(rz, Relation::GreaterEqual, 1.0);
    s.assertAtom(zlo, true);
    require(s.dormantRowCount() == 2, "appended row activated by its bound");
    require(s.check(observer) == FloatSimplex::Verdict::Feasible, "appended dormant feasible");
    require(s.assignmentOf(z).value >= 1.0 - 1e-9, "appended row bound respected");
    s.undoTo(0);
    s.setDormantRows(false);
    require(s.dormantRowCount() == 0, "disable relinks every row");
    require(s.check(observer) == FloatSimplex::Verdict::Feasible, "relinked tableau feasible");
    s.setDormantRows(true);
    s.switchToFactorized();
    require(s.dormantRowCount() == 0, "factorized mode has no dormant rows");
    s.assertAtom(f.sum_le3, true);
    s.assertAtom(f.x_ge2, true);
    s.assertAtom(f.y_ge2, true);
    require(s.check(observer) == FloatSimplex::Verdict::InfeasibleCandidate,
            "factorized verdict unchanged under the flag");
  }
}

void testDormantMinCells()
{
  /* Fixture rows: r1 = x + y (2 cells), r2 = x, r3 = y (1 cell each).  With
   * a width gate of 2 only r1 starts dormant; the narrow rows stay live,
   * and an appended narrow row is live while an appended wide one sleeps. */
  PermissiveObserver observer;
  Fixture f;
  auto& s = f.simplex;
  s.setDormantRows(true, 2);
  require(s.dormantMinCells() == 2, "min cells recorded");
  require(s.dormantRowCount() == 1, "only the two-cell row starts dormant");
  s.assertAtom(f.x_ge2, true);
  require(s.rowActivations() == 0, "a live narrow row needs no activation");
  s.assertAtom(f.sum_le3, true);
  require(s.rowActivations() == 1 && s.dormantRowCount() == 0, "the wide row wakes on its bound");
  s.assertAtom(f.y_ge2, true);
  require(s.check(observer) == FloatSimplex::Verdict::InfeasibleCandidate, "gated: conflict found");
  s.undoTo(0);
  auto z = s.addColumn(), w = s.addColumn();
  FloatSimplex::Term tz{z, 1.0};
  s.addRow(&tz, &tz + 1);
  require(s.dormantRowCount() == 0, "appended narrow row is live");
  FloatSimplex::Term tzw[] = {{z, 1.0}, {w, 1.0}};
  s.addRow(tzw, tzw + 2);
  require(s.dormantRowCount() == 1, "appended wide row starts dormant");
  s.restartBasis();
  require(s.dormantRowCount() == 2, "restart re-dormants the wide rows only");
  require(s.check(observer) == FloatSimplex::Verdict::Feasible, "gated restart feasible");
}

}  // namespace

int main()
{
  try
  {
    testDormantMinCells();
    testDormantRows();
    testEarlyConflict();
    testSoi();
    testPersistentExtension();
    testDecisionPolarity();
    exerciseOneMode(/*factorized=*/false);
    exerciseOneMode(/*factorized=*/true);
  }
  catch (const std::exception& failure)
  {
    std::fprintf(stderr, "float simplex test failure: %s\n",
                 failure.what());
    return 1;
  }
  std::puts("float simplex tests passed");
  return 0;
}
