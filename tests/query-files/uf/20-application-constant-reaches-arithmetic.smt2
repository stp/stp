; An application pinned to a constant at the top level is that constant
; everywhere else, so the divisor below folds to 1 and the quotient to w
; before anything is bit-blasted. Lowering would have hidden (f #x03) behind
; a protected result symbol, and the divider would have been built.
;
; RUN: %solver -s --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver -s --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: UF: pre-lowering substituted 1 symbol\(s\) and 1 application\(s\)
; CHECK: ^unsat$
;
; EXPECT: unsat
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-const w (_ BitVec 8))
(declare-const z (_ BitVec 8))
(assert (= (f #x03) #x00))
(assert (= z (bvudiv w (bvadd (f #x03) #x01))))
(assert (distinct z w))
(check-sat)
