; The cases at the edge of the ordering rewrite's guard.
;
; Two groups sharing an operand are each symmetric on their own and not
; symmetric together: ordering both would fix a < b < c and c < b < d at once,
; which no assignment satisfies, so a query that is plainly sat would come back
; unsat. Neither is taken -- the operand belongs to neither group exclusively.
;
; A repeated operand makes the distinct false, not symmetric. That block is
; pinned by the absence of the stats line rather than by its answer: unsat is
; correct, and a < b < a would be unsat too, so only the CHECK-NOT says the
; candidate test rejected it instead of ordering it by accident.
;
; Two independent groups over disjoint operands are both taken, which is what
; says the overlap rule rejects sharing rather than plurality.
;
; The last block is the one the overlap rule cannot decide. p occurs nowhere
; but inside two distincts, and the second has a compound operand, so p is not
; among the names that rule compares -- it has to be found by descending into
; that distinct instead. Only the group that really is isolated is ordered.
;
; RUN: %solver -s --incremental=off %s 2>&1 | %OutputCheck %s
; CHECK-NOT: Ordered
; CHECK: ^sat
; CHECK: OVERLAP-DONE
; CHECK-NOT: Ordered
; CHECK: ^unsat
; CHECK: REPEAT-DONE
; CHECK: Ordered 2 symmetric distinct group\(s\)
; CHECK: ^sat
; CHECK: PLURAL-DONE
; CHECK: Ordered 1 symmetric distinct group\(s\)
; CHECK: ^sat
;
(set-logic QF_BV)
(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
(declare-const c (_ BitVec 8))
(declare-const d (_ BitVec 8))
(assert (distinct a b c))
(assert (distinct c b d))
(check-sat)
(echo "OVERLAP-DONE")
(reset)
(set-logic QF_BV)
(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
(assert (distinct a b a))
(check-sat)
(echo "REPEAT-DONE")
(reset)
(set-logic QF_BV)
(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
(declare-const c (_ BitVec 8))
(declare-const p (_ BitVec 8))
(declare-const q (_ BitVec 8))
(declare-const r (_ BitVec 8))
(assert (distinct a b c))
(assert (distinct p q r))
(check-sat)
(echo "PLURAL-DONE")
(reset)
(set-logic QF_BV)
(declare-const p (_ BitVec 8))
(declare-const q (_ BitVec 8))
(declare-const r (_ BitVec 8))
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(declare-const u (_ BitVec 8))
(declare-const v (_ BitVec 8))
(declare-const w (_ BitVec 8))
(assert (distinct p q r))
(assert (distinct (bvadd p #x01) x y))
(assert (distinct u v w))
(check-sat)
