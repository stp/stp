; The array-equality checker is never handed a candidate an abstraction has
; not been refined against.
;
; The complete array checker owns every read of an active equality solve, and
; it reads the candidate through the scalar names the lowering gave those
; reads. Under --bv-eq-abstraction the equality that names a scalar is one of
; the equalities replaced by a free Boolean, so until refinement pins it the
; solver may set the Boolean and the bits it stands for independently. What
; the checker then reads is not an assignment of the query at all, and it
; reports so as an internal error rather than as a third refinement outcome:
;
;   Fatal Error: array-equality: the checker could neither certify nor refute
;   a materialized candidate
;
; It is entitled to: every other producer of a candidate hands it a faithful
; bit-vector layer. So the abstraction is refined first, inside the same call
; that materialized the candidate, and a candidate that contradicts one is
; ruled out before the checker, the UF checker, or model evaluation sees it.
;
; Two unconstrained arrays asserted distinct is enough -- the disequality's
; witness read is the access the checker works on.
;
; RUN: %solver --incremental=off -d --array-equality --bv-eq-abstraction=1 --bv-abstraction-width=1 %s 2>&1 | %OutputCheck --check-prefix=ABSTRACTED %s
; RUN: %solver --incremental=off -d --array-equality %s 2>&1 | %OutputCheck --check-prefix=PLAIN %s
;
; ABSTRACTED-NOT: Fatal Error
; ABSTRACTED-NOT: Assertion
; ABSTRACTED: ^sat$
;
; PLAIN: ^sat$
;
(set-logic QF_ABV)
(declare-const a (Array (_ BitVec 1) (_ BitVec 1)))
(declare-const b (Array (_ BitVec 1) (_ BitVec 1)))
(assert (distinct a b))
(check-sat)
