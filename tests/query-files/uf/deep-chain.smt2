; RUN: %solver --uninterpreted-functions --incremental=off %s | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s | %OutputCheck %s
; RUN: %solver --uninterpreted-functions %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; A deeper hidden application chain exercises completed-root traversal and
; the up-front registration needed to read every checker scalar.
(set-logic QF_UFBV)
(declare-fun g ((_ BitVec 4)) (_ BitVec 4))
(declare-fun f ((_ BitVec 4)) (_ BitVec 4))
(declare-fun x () (_ BitVec 4))
(declare-fun y () (_ BitVec 4))
(assert (= x y))
(assert (distinct (f (g (f (g x)))) (f (g (f (g y))))))
(check-sat)
