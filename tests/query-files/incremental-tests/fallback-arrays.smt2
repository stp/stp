; Mixed rounds: array levels appear mid-session (handled natively by the
; incremental driver since phase 3; before that, via batch fallback) and
; are popped away again. Answers must be right throughout, whichever
; engine serves each round.
; RUN: %solver %s | %OutputCheck %s
(set-logic QF_ABV)
(declare-fun x () (_ BitVec 8))
(assert (bvult x #x10))
(push 1)
; CHECK-NEXT: ^sat
(check-sat)
(push 1)
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
(assert (= (select a x) #xff))
(assert (= (select a #x00) #x01))
; CHECK-NEXT: ^sat
(check-sat)
(assert (= x #x00))
; a[x]=ff and a[0]=01 with x=0 is contradictory
; CHECK-NEXT: ^unsat
(check-sat)
(pop 1)
; arrays gone: back on the incremental path
; CHECK-NEXT: ^sat
(check-sat)
(push 1)
(assert (bvugt x #x20))
; CHECK-NEXT: ^unsat
(check-sat)
(pop 1)
(pop 1)
(exit)
