; RUN: %solver --incremental=on --fp-abstraction=true --fp-abstraction-incremental=true %s | %OutputCheck %s
; RUN: %solver --incremental=on --fp-abstraction=true --fp-abstraction-incremental=true --fp-abstraction-ops=mul,div,sqrt,fma,add %s | %OutputCheck %s
;
; Two formats in one session: a binary32 product is abstracted while the
; binary64 sum stays exact by default (and is abstracted under the wider
; ops mask on the second run); either way every answer is the exact
; pipeline's, and the unsat needs facts about both.
; CHECK: ^sat
; CHECK: ^sat
; CHECK: ^unsat
(set-logic QF_BVFP)
(set-option :global-declarations true)
(declare-const x (_ FloatingPoint 8 24))
(declare-const w (_ FloatingPoint 11 53))
(declare-const p (_ FloatingPoint 8 24))
(declare-const s (_ FloatingPoint 11 53))
(push 1)
(assert (= p (fp.mul RNE x x)))
(assert (fp.isNormal x))
(check-sat)
(push 1)
(assert (= s (fp.add RNE w w)))
(assert (fp.isNormal w))
(assert (fp.gt w (fp #b0 #b01111111111 #x0000000000000)))
(check-sat)
(push 1)
(assert (fp.lt p (fp #b1 #x00 #b00000000000000000000000)))
(check-sat)
(exit)
