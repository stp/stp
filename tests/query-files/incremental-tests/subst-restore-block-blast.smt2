; The exact-stack block encodes the RAW base -- eliminated defining
; equations included -- so a whole-array-equality round can mint SAT bits
; for a variable sigma0 substituted away. Inside the block those bits are
; constrained only under the block's retractable literal; the ordinary
; round afterwards must not read them into the model unconstrained. The
; restoration guard re-asserts the equation as a permanent unit when the
; block first mentions the variable raw, so the final model reports
; x = 255 by constraint rather than by the accident of saved phases.
; RUN: %solver --incremental --array-equality %s | %OutputCheck %s
; RUN: %solver --incremental --array-equality --check-sanity %s | %OutputCheck %s
(set-option :produce-models true)
(set-logic QF_ABV)
(declare-fun x () (_ BitVec 8))
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun b () (Array (_ BitVec 8) (_ BitVec 8)))
(assert (= x #xff))
; CHECK-NEXT: ^sat
(check-sat)
(push 1)
(assert (= a b))
; CHECK-NEXT: ^sat
(check-sat)
(pop 1)
; CHECK-NEXT: ^sat
(check-sat)
; CHECK: \|x\| +#xFF
(get-value (x))
(exit)
