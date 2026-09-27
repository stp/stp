; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; The same array cannot read anything but the default: a read that reaches the
; constant array must carry the default (checker rule K).
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun i () (_ BitVec 8))
(assert (= a ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x07)))
(assert (not (= (select a i) #x07)))
(check-sat)
