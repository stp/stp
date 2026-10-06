; Named assertions that contradict each other, over reads of rounding-mode
; write chains. With unsat cores on, named assertions are tracked as one
; unsimplified level so that each is its own root, and that level reached
; the driver's array test intact. Totalised whole it folded to FALSE, which
; has no arrays, so the solve skipped array refinement while the two roots
; still read the chains through abstractions only refinement relates: the
; answer was sat. See contradictory-assumptions-over-arrays.smt2.
; RUN: %solver %s | %OutputCheck %s
(set-option :produce-unsat-cores true)
(declare-const a (Array RoundingMode RoundingMode))
(declare-const x RoundingMode)
(declare-const y RoundingMode)
(declare-const z RoundingMode)
(define-fun l () RoundingMode
  (select (store (store (store (store a x x) z RTN) RTN y) z y)
          (select (store (store (store (store a RTN RTN) z RTN) x y) z x) y)))
(define-fun r () RoundingMode
  (select (store (store (store (store a x x) y z) x x) z z) RTN))
(assert (! (= l r) :named eq))
(assert (! (distinct l r) :named ne))
(check-sat)
; CHECK: ^unsat$
(get-unsat-core)
; CHECK-NEXT: ^\(\|eq\| \|ne\|\)$
