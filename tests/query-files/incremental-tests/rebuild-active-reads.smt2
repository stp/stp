; A relief-valve rebuild must refresh the active-read accounting transaction.
; The first solve folds the permanent base row A[i+1]. Growing the base with
; i=0 does not change that already encoded root. At the rebuild, however, the
; same base assertion re-encodes to A[1]. Keeping its old folded-row record
; seeds the stale A[i+1] row into refinement and omits the live replacement,
; which makes model checking reject a candidate with no axiom available.
;
; RUN: %solver -s --incremental --incremental-reencode-limit 1 %s 2>&1 | %OutputCheck %s
; RUN: %solver -s --incremental-auto-engage-at 1 --incremental-reencode-limit 1 %s 2>&1 | %OutputCheck %s
(set-logic QF_ABV)
(declare-fun A () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun i () (_ BitVec 4))
(declare-fun y0 () (_ BitVec 12))
(declare-fun y1 () (_ BitVec 12))
(declare-fun y2 () (_ BitVec 12))
(declare-fun y3 () (_ BitVec 12))
(declare-fun y4 () (_ BitVec 12))
(declare-fun y5 () (_ BitVec 12))

(assert (= (select A (bvadd i #x1)) #x01))
; CHECK: ^sat
(check-sat)

; The later permanent definition changes the row touched when the base root is
; next encoded from scratch.
(assert (= i #x0))

(push 1)
(assert (bvugt (bvmul y0 y0) #x003))
; CHECK: ^sat
(check-sat)
(pop 1)

(push 1)
(assert (bvugt (bvmul y1 y1) #x003))
; CHECK: ^sat
(check-sat)
(pop 1)

(push 1)
(assert (bvugt (bvmul y2 y2) #x003))
; CHECK: ^sat
(check-sat)
(pop 1)

(push 1)
(assert (bvugt (bvmul y3 y3) #x003))
; CHECK: ^sat
(check-sat)
(pop 1)

(push 1)
(assert (bvugt (bvmul y4 y4) #x003))
; CHECK: ^sat
(check-sat)
(pop 1)

(push 1)
(assert (bvugt (bvmul y5 y5) #x003))
; CHECK: re-encoded from scratch
; CHECK: ^sat
(check-sat)
(pop 1)
(exit)
