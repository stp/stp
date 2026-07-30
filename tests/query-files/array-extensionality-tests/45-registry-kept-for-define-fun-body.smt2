; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK: ^sat
; CHECK: ^unsat
; The companion to 44: retiring the registry must not go by the
; assertion stack alone. Here the only mention of the array equality
; when the pop happens is the body of an outer-level define-fun, which
; is asserted afterwards. Counting the stored function bodies as live
; is what keeps the record; without them the abstraction variable
; becomes an unconstrained Boolean, p = r stops constraining anything,
; and the second query answers sat instead of unsat.
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
