; RUN: %solver %s | %OutputCheck %s
;
; The pinned cell contradicts a direct read of the same index.
;
; CHECK: ^unsat
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
(assert (= a (store a #x03 #x2a)))
(assert (= (select a #x03) #x2b))
(check-sat)
(exit)
