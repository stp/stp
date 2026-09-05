; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; The substitution orientation that must stay refused while the checker
; owns the array graph: READ(Arr, const) |-> BVCONST.
;
; TermOrder makes a read the substitution key only in this shape. Taking
; it deletes the read from the formula and bakes its value in, so the
; checker never registers an access at that cell -- and here both
; equations would go, leaving a formula that is trivially true with the
; equality's abstraction variable unconstrained. The answer would flip
; to sat.
;
; a and b are equal, so they cannot disagree at index 0.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun b () (Array (_ BitVec 4) (_ BitVec 8)))
(assert (= a b))
(assert (= (select a #x0) #x05))
(assert (= (select b #x0) #x07))
(check-sat)
