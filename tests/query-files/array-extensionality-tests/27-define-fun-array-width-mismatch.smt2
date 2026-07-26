; RUN: %solver --array-equality %s 2>&1 | %OutputCheck %s
; CHECK-L: Different array widths specified: (2 2) vs (3 2)
; CHECK-L: sat
; The declared result sort disagrees with the body's sort: the parser
; reports the mismatch with both sort pairs and -- mirroring the
; sibling bitvector define-fun productions -- still stores the
; function and keeps parsing, so the check-sat below is answered.
(set-logic QF_ABV)
(declare-fun base () (Array (_ BitVec 2) (_ BitVec 2)))
(define-fun A0 () (Array (_ BitVec 3) (_ BitVec 2)) (store base #b00 #b01))
(check-sat)
