; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; A checker-owned read whose abstraction variable appears only inside another
; read's index: the refinement lemma for the store congruence must be
; encodable over that variable even though nothing else carries it
; into the bit-blasted formula. The equality itself is false (the two
; stores differ at index zero), so the query is unsatisfiable.
(declare-const i (_ BitVec 2))
(declare-const x (Array (_ BitVec 2) (_ BitVec 2)))
(declare-const x9 (Array (_ BitVec 2) (_ BitVec 2)))
(assert (= (select x9 (select (store x (_ bv0 2) (_ bv0 2)) i)) (_ bv0 2)))
(assert (= (store x (_ bv0 2) (_ bv0 2)) (store x (_ bv0 2) (_ bv1 2))))
(check-sat)
