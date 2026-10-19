; REQUIRES: kissat
; RUN: %solver --kissat --incremental=on --bv-eq-abstraction=1 --bv-abstraction-width=1 -d %s | %OutputCheck %s
; RUN: %solver --kissat --incremental=on --refinement-trail-reuse=0 --kissat-factor=off -d %s | %OutputCheck %s
; CHECK: ^sat$
; CHECK-NEXT: ^unsat$
; CHECK-NEXT: ^sat$
; CHECK-NEXT: ^unsat$
; CHECK-NEXT: ^sat$
(set-logic QF_ABV)
(declare-const memory (Array (_ BitVec 8) (_ BitVec 8)))
(declare-const i (_ BitVec 8))
(declare-const j (_ BitVec 8))
(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
(assert (= (bvmul a b) #x21))
(assert (bvult a b))
(define-fun updated () (Array (_ BitVec 8) (_ BitVec 8))
  (store memory i (bvmul a b)))
(assert (distinct (select updated j) #x21))
(check-sat)
(push 1)
(assert (= i j))
(check-sat)
(pop 1)
(check-sat)
(push 1)
(assert (distinct (select updated i) #x21))
(check-sat)
(pop 1)
(check-sat)
