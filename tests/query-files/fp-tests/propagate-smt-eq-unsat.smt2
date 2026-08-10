; RUN: %solver --exit-after-CNF %s | %OutputCheck %s
; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --disable-simplifications %s | %OutputCheck %s
;
; The wintersteiger "has-no-other-solution" shape: variables pinned to
; literals by SMT =, and the operation's result asserted NOT equal to the
; known answer. Propagation makes the operands constant, the fp.add folds,
; and the negated equality is refuted before CNF (first RUN prints unsat
; only if that whole chain fires). 1.5 + 1.5 = 3.0 exactly at binary32.
;
; CHECK: ^unsat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(declare-fun r () (_ FloatingPoint 8 24))
(assert (= x (fp #b0 #b01111111 #b10000000000000000000000)))
(assert (= y (fp #b0 #b01111111 #b10000000000000000000000)))
(assert (= r (fp #b0 #b10000000 #b10000000000000000000000)))
(assert (not (= (fp.add RNE x y) r)))
(check-sat)
(exit)
