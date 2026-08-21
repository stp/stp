; The driver's array-equality round refines the abstraction before its
; checker sees the candidate.
;
; A whole-array equality routes the check through the exact-stack block, where
; the extensionality checker owns the complete array graph and every candidate
; is its to certify or refute. Under --bv-eq-abstraction the equations naming
; the graph's scalars are among the equalities replaced by free Booleans, and
; with nothing refining them the checker was reading names that had drifted
; away from the terms they stand for:
;
;   Fatal Error: array-equality: a scalar name disagrees with its term after
;   the complete array graph reached a conflict-free fixed point
;
; and, on the same route, a lemma assembled over such a name:
;
;   Fatal Error: array-equality: a lemma premise was structurally decided
;   against the polarity the conflict needs
;
; Neither guard is wrong. The abstraction is now refined inside the round that
; materialized the candidate and ahead of the checker, so what the checker
; reads is an assignment of the query.
;
; The store chain is load-bearing: it is what gives the round enough accesses
; for the checker to have something to say while the abstraction still does.
;
; RUN: %solver --incremental=on --array-equality -d --bv-eq-abstraction=1 --bv-abstraction-width=1 %s 2>&1 | %OutputCheck --check-prefix=ABSTRACTED %s
; RUN: %solver --incremental=on --array-equality -d %s 2>&1 | %OutputCheck --check-prefix=PLAIN %s
;
; ABSTRACTED-NOT: Fatal Error
; ABSTRACTED-NOT: Assertion
; ABSTRACTED: ^sat$
;
; PLAIN: ^sat$
;
(set-logic QF_ABV)
(declare-const x (_ BitVec 4))
(declare-const a (Array (_ BitVec 4) (_ BitVec 4)))
(declare-const y (_ BitVec 4))
(assert (let ((w (store a x #b0001)))
  (= a (store (store (store (store (store w (bvudiv x x) #b0001) #b0001 x) y #b0000) (bvsmod x x) x) (bvneg (_ bv10 4)) x)
       (store w (_ bv5 4) x))))
(check-sat)
(exit)
