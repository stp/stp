; RUN: %solver --incremental=on --fp-abstraction=true --fp-abstraction-incremental=true -s %s 2>&1 | %OutputCheck %s
; RUN: %solver --incremental=on --fp-abstraction=true --fp-abstraction-incremental=true -d %s | %OutputCheck %s
;
; The abstraction hosted by the driver: a product is recorded once, its
; record persists across the levels of a monotone session, and the answers
; are the exact pipeline's. The final level pins the product to a value
; the operands cannot give, so the last check is unsatisfiable and must be
; refuted through the record's lemmas or its release.
; CHECK: ^sat
; CHECK: ^sat
; CHECK: ^sat
; CHECK: ^unsat
(set-logic QF_BVFP)
(set-option :global-declarations true)
(declare-const x (_ FloatingPoint 8 24))
(declare-const y (_ FloatingPoint 8 24))
(declare-const t (_ FloatingPoint 8 24))
(push 1)
(assert (= t (fp.mul RNE x y)))
(check-sat)
(push 1)
(assert (fp.isNormal x))
(assert (fp.isNormal y))
(assert (fp.gt x (fp #b0 #x7f #b00000000000000000000000)))
(assert (fp.gt y (fp #b0 #x7f #b00000000000000000000000)))
(check-sat)
(push 1)
(assert (fp.gt t (fp #b0 #x7f #b00000000000000000000000)))
(check-sat)
(push 1)
(assert (fp.lt t (fp #b0 #x7e #b00000000000000000000000)))
(check-sat)
(exit)
