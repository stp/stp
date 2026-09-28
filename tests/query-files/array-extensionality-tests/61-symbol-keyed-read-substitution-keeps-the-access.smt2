; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; The companion orientation, which is allowed: "v |-> READ(A, i)".
;
; This one deletes no access. The read is copied to wherever the symbol
; occurred, so it still reaches the checker and still has to agree
; across the equality; if the symbol occurred nowhere else, the read
; constrained nothing to begin with. Refusing it as well -- which a bare
; "either side is a READ" test does -- suppressed ordinary bit-vector
; solving over every read in the query.
;
; Both defining equations are substituted away, leaving the disequality
; over two reads that a true array equality forces to agree.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun b () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun v () (_ BitVec 8))
(declare-fun w () (_ BitVec 8))
(assert (= a b))
(assert (= v (select a #x0)))
(assert (= w (select b #x0)))
(assert (distinct v w))
(check-sat)
