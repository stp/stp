; RUN: %solver --array-equality %s | %OutputCheck %s
;
; The fold preempts the whole-array-equality machinery when the flag is
; on: same answer, and no extensionality lemmas are needed for it.
;
; CHECK: ^unsat
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
(assert (= a (store a #x03 #x2a)))
(assert (= (select a #x03) #x2b))
(check-sat)
(exit)
