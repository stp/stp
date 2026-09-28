; Dependency closure crosses the Boolean/bit-vector abstraction families.
; Each first leg creates and then retracts an inner multiplication. The second
; leg reuses it below, respectively, an abstracted equality, comparison and
; bit-vector ITE. The active root directly owns only that outer producer; the
; multiplication must be reactivated through the recorded dependency edge.
;
; RUN: %solver --incremental=on --disable-simplifications --bv-eq-abstraction=1 --bv-term-abstraction=1 --bv-abstraction-width=8 --bv-term-abstraction-schemas=0 --bv-term-abstraction-rounds=4 %s 2>&1 | %OutputCheck --check-prefix=ABSTRACTED %s
; RUN: %solver --incremental=off --disable-simplifications %s 2>&1 | %OutputCheck --check-prefix=EXACT %s
;
; ABSTRACTED: ^sat$
; ABSTRACTED-NEXT: ^unsat$
; ABSTRACTED-NEXT: ^sat$
; ABSTRACTED-NEXT: ^unsat$
; ABSTRACTED-NEXT: ^sat$
; ABSTRACTED-NEXT: ^unsat$
;
; EXACT: ^sat$
; EXACT-NEXT: ^unsat$
; EXACT-NEXT: ^sat$
; EXACT-NEXT: ^unsat$
; EXACT-NEXT: ^sat$
; EXACT-NEXT: ^unsat$

(set-logic QF_BV)

(declare-fun ex () (_ BitVec 8))
(declare-fun ey () (_ BitVec 8))
(push 1)
(assert (= ex #x01))
(assert (= ey #x01))
(assert (= ((_ extract 0 0) (bvmul ex ey)) #b1))
(check-sat)
(pop 1)
(push 1)
(assert (= ex #x00))
(assert (= ey #x01))
(assert (= (bvmul ex ey) #x01))
(check-sat)
(pop 1)

(declare-fun cx () (_ BitVec 8))
(declare-fun cy () (_ BitVec 8))
(push 1)
(assert (= cx #x01))
(assert (= cy #x01))
(assert (= ((_ extract 0 0) (bvmul cx cy)) #b1))
(check-sat)
(pop 1)
(push 1)
(assert (= cx #x00))
(assert (= cy #x01))
(assert (bvugt (bvmul cx cy) #x00))
(check-sat)
(pop 1)

(declare-fun ix () (_ BitVec 8))
(declare-fun iy () (_ BitVec 8))
(declare-fun choose () Bool)
(push 1)
(assert (= ix #x01))
(assert (= iy #x01))
(assert (= ((_ extract 0 0) (bvmul ix iy)) #b1))
(check-sat)
(pop 1)
(push 1)
(assert (= ix #x00))
(assert (= iy #x01))
(assert choose)
(assert (= ((_ extract 0 0) (ite choose (bvmul ix iy) #xff)) #b1))
(check-sat)
(pop 1)
(exit)
