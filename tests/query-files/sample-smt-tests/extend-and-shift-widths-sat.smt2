; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^sat
;
; sign_extend and zero_extend at a real width and at the zero width the
; standard allows, and shifts by amounts that do not fit in 32 bits.
; Converted from the SMT-LIB 1 working_55.smt.
(set-logic QF_BV)
(set-info :status sat)

; sym1 = 0xF..F.
(declare-fun sym1 () (_ BitVec 64))
(assert (= sym1 ((_ sign_extend 63) #b1)))
(assert (= sym1 (bvnot #x0000000000000000)))

; sym2 = 0x0..01
(declare-fun sym2 () (_ BitVec 64))
(assert (= sym2 ((_ zero_extend 63) #b1)))

; A zero-width extension is the identity.
(assert (= sym1 ((_ zero_extend 0) sym1)))
(assert (= sym1 ((_ sign_extend 0) sym1)))

; A shift by an amount wider than 32 bits.
(declare-fun sym3 () (_ BitVec 64))
(assert (= sym3 (bvshl #x0000000000000001 #x000000000000003F)))
(declare-fun sym4 () (_ BitVec 64))
(assert (= sym4 (bvlshr #x0000000000000001 #x000000000000003F)))

; Zero- and sign-extending a 63-bit value to 64 bits agree only when its top
; bit is clear.
(declare-fun sym6 () (_ BitVec 64))
(declare-fun sym7 () (_ BitVec 63))
(assert (= sym6 ((_ zero_extend 1) sym7)))
(assert (= sym6 ((_ sign_extend 1) sym7)))
(check-sat)
(exit)
