; RUN: %solver -d %s | %OutputCheck %s
;
; Negated: the cell must differ from the value, which the model check
; reconstructs.
;
; CHECK: ^sat
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
(assert (not (= (store a #x03 #x2a) a)))
(check-sat)
(exit)
