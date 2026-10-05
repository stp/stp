; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --incremental %s | %OutputCheck %s
; CHECK: ^unsat
;
; The same store, where treating it as free changes the answer. c holds
; i+1 at every index i, so it has no cell holding its own index, while
; (store b x x) holds x at x: they cannot be equal. RemoveUnconstrained
; took b and x for unconstrained, replaced the store with a fresh array
; free to equal c, and answered sat. The model check on that route covers
; only the rewritten formula, so the cyclic definition x := v[x] it left
; behind went unnoticed.
(set-logic QF_ABV)
(declare-fun b () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun d () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun x () (_ BitVec 2))
(assert (= (store b x x)
           (store (store (store (store d #b00 #b01) #b01 #b10) #b10 #b11)
                  #b11 #b00)))
(check-sat)
