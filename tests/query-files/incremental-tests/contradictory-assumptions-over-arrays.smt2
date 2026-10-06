; Assumptions that contradict each other, over reads of rounding-mode write
; chains. The assumption level is kept unsimplified so that each assumption
; is its own root and an unsat core can name it, but the driver judged
; whether the stack had arrays on that level's totalised whole, which the
; simplifying factory folds to FALSE: no arrays, so the solve skipped array
; refinement, while each of the two roots still read the chains -- one
; expanded eagerly, the next abstracted -- and nothing tied them together.
; Both were satisfied and the answer was sat.
; The second check is contradictory only once DISTINCT is lowered, and the
; third must still report just the two assumptions that conflict.
; RUN: %solver --incremental %s | %OutputCheck %s
(set-option :produce-unsat-assumptions true)
(declare-const a (Array RoundingMode RoundingMode))
(declare-const x RoundingMode)
(declare-const y RoundingMode)
(declare-const z RoundingMode)
(declare-const q Bool)
(define-fun l () RoundingMode
  (select (store (store (store (store a x x) z RTN) RTN y) z y)
          (select (store (store (store (store a RTN RTN) z RTN) x y) z x) y)))
(define-fun r () RoundingMode
  (select (store (store (store (store a x x) y z) x x) z z) RTN))
(check-sat-assuming ((= l r) (not (= l r))))
; CHECK: ^unsat$
(check-sat-assuming ((= l r) (distinct l r) q))
; CHECK-NEXT: ^unsat$
; The core ends at the distinct, so q is not in it.
(get-unsat-assumptions)
; CHECK-NEXT: ^\(\(= .*\) \(distinct .*\)\)$
(check-sat-assuming ((distinct l r) q))
; CHECK-NEXT: ^sat$
