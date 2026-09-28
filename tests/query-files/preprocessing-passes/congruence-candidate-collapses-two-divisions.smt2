; Two divisions by the same divisor whose dividends are equal and spelled
; differently. The query never says they are equal, so each is its own
; divider and the SAT solver has to reason through both.
;
; That the query applies bvudiv to both in the same position with the same
; divisor is what makes them worth comparing: the pairing is one the formula
; chose. The equality is then proved as its own query and asserted, and the
; two divisions become one.
; RUN: %solver -s --congruence-candidates=1 %s 2>&1 | %OutputCheck %s
; CHECK: proved:[1-9]
; CHECK: After Congruence Candidates
; CHECK: ^unsat$
;
; Only theorems are asserted, so the answer is the same with the pass off.
; RUN: %solver %s | %OutputCheck --check-prefix=OFF %s
; OFF: ^unsat$
(set-logic QF_BV)
(declare-fun a () (_ BitVec 16))
(declare-fun b () (_ BitVec 16))
(declare-fun d () (_ BitVec 16))
(assert
  (not (=
    (bvudiv (bvadd (bvmul (_ bv3 16) a) (bvsub b a)) d)
    (bvudiv (bvadd (bvadd a a) (bvadd b (_ bv0 16))) d))))
(check-sat)
(exit)
