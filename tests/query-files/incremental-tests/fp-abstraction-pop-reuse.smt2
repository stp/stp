; RUN: %solver --incremental=on --fp-abstraction=true --fp-abstraction-incremental=true %s | %OutputCheck %s
; RUN: %solver --incremental=on --fp-abstraction=true --fp-abstraction-incremental=true -d %s | %OutputCheck %s
;
; A popped contradiction must not outlive its level: the pushed level pins
; the quotient to an impossible value (unsat), the pop retracts it, and the
; same stack re-pushed with a satisfiable bound reuses the record with
; everything it learned. A lemma or release wrongly scoped to the popped
; level would turn the third answer wrong; a blocking fact wrongly kept
; permanent without its symbols would turn the second solve's re-push unsat.
; CHECK: ^sat
; CHECK: ^unsat
; CHECK: ^sat
; CHECK: ^unsat
(set-logic QF_BVFP)
(set-option :global-declarations true)
(declare-const a (_ FloatingPoint 8 24))
(declare-const b (_ FloatingPoint 8 24))
(declare-const q (_ FloatingPoint 8 24))
(push 1)
(assert (= q (fp.div RNE a b)))
(assert (fp.isNormal a))
(assert (fp.isNormal b))
(assert (fp.gt a (fp #b0 #x7f #b00000000000000000000000)))
(assert (fp.gt b (fp #b0 #x7f #b00000000000000000000000)))
(check-sat)
(push 1)
(assert (fp.isNaN q))
(check-sat)
(pop 1)
(push 1)
(assert (fp.isNormal q))
(check-sat)
(push 1)
(assert (fp.isInfinite q))
(check-sat)
(exit)
