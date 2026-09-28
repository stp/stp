; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK: ^sat
; CHECK: ^unsat
; The companion to 44: an outer-level define-fun retains its opaque array
; equality across a pushed assertion scope. The first solve does not expand or
; lower that dormant body. When the function is asserted afterwards, query
; construction expands it and solve-boundary lowering creates the equality's
; fresh record and witness bundle; lowering the assertion stack alone would
; miss it and leave p = r unconstrained.
(set-logic QF_ABV)
(declare-fun p () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun r () (Array (_ BitVec 4) (_ BitVec 8)))
(define-fun same () Bool (= p r))
(push 1)
(assert (= (select p #x0) #x01))
(check-sat)
(pop 1)
(assert same)
(assert (not (= (select p #x0) (select r #x0))))
(check-sat)
