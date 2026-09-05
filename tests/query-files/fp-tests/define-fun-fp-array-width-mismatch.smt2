; RUN: %solver %s 2>&1 | %OutputCheck %s
; CHECK-L: Different array widths specified: (2 32) vs (3 32)
; CHECK-L: sat
; The declared result sort disagrees with the body's: the parser
; reports the mismatch with both sort pairs -- the element width being
; the float's packed width -- and, mirroring the sibling bitvector
; define-fun productions, still stores the function and keeps parsing,
; so the check-sat below is answered.
(set-logic QF_ABVFP)
(declare-fun base () (Array (_ BitVec 2) (_ FloatingPoint 8 24)))
(define-fun A0 () (Array (_ BitVec 3) (_ FloatingPoint 8 24)) (store base #b01 (_ +zero 8 24)))
(check-sat)
