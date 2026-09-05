; REQUIRES: cadical
; Inprocessing retirement targets many variants over a fixed permanent base:
; re-probing that same encoding each time is recurring work. It must stay on
; while level zero is still growing, because the new permanent clauses give
; preprocessing useful work and later proof obligations may depend on it.
;
; This is the complement of inprobing-retire.smt2. The FP multipliers cross
; the same solver-size and solve-count thresholds, but a fresh permanent unit
; arrives between every query. Neither the ninth nor tenth check may rebuild
; to retire inprocessing.
; RUN: %solver --cadical --incremental --incremental-profile %s 2>&1 | %OutputCheck %s
(set-logic QF_BVFP)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(declare-fun b1 () Bool)
(declare-fun b2 () Bool)
(declare-fun b3 () Bool)
(declare-fun b4 () Bool)
(declare-fun b5 () Bool)
(declare-fun b6 () Bool)
(declare-fun b7 () Bool)
(declare-fun b8 () Bool)
(declare-fun b9 () Bool)

(push 1)
(assert (fp.lt (fp.mul RNE x (fp.add RNE y (fp #b0 #x7f #b00000000000000000000001))) (fp #b0 #x82 #b00000000000000000000000)))
; CHECK: ^sat
(check-sat)
(pop 1)
(assert b1)
(push 1)
(assert (fp.lt (fp.mul RNE x (fp.add RNE y (fp #b0 #x7f #b00000000000000000000010))) (fp #b0 #x82 #b00000000000000000000000)))
; CHECK: ^sat
(check-sat)
(pop 1)
(assert b2)
(push 1)
(assert (fp.lt (fp.mul RNE x (fp.add RNE y (fp #b0 #x7f #b00000000000000000000011))) (fp #b0 #x82 #b00000000000000000000000)))
; CHECK: ^sat
(check-sat)
(pop 1)
(assert b3)
(push 1)
(assert (fp.lt (fp.mul RNE x (fp.add RNE y (fp #b0 #x7f #b00000000000000000000100))) (fp #b0 #x82 #b00000000000000000000000)))
; CHECK: ^sat
(check-sat)
(pop 1)
(assert b4)
(push 1)
(assert (fp.lt (fp.mul RNE x (fp.add RNE y (fp #b0 #x7f #b00000000000000000000101))) (fp #b0 #x82 #b00000000000000000000000)))
; CHECK: ^sat
(check-sat)
(pop 1)
(assert b5)
(push 1)
(assert (fp.lt (fp.mul RNE x (fp.add RNE y (fp #b0 #x7f #b00000000000000000000110))) (fp #b0 #x82 #b00000000000000000000000)))
; CHECK: ^sat
(check-sat)
(pop 1)
(assert b6)
(push 1)
(assert (fp.lt (fp.mul RNE x (fp.add RNE y (fp #b0 #x7f #b00000000000000000000111))) (fp #b0 #x82 #b00000000000000000000000)))
; CHECK: ^sat
(check-sat)
(pop 1)
(assert b7)
(push 1)
(assert (fp.lt (fp.mul RNE x (fp.add RNE y (fp #b0 #x7f #b00000000000000000001000))) (fp #b0 #x82 #b00000000000000000000000)))
; CHECK: ^sat
(check-sat)
(pop 1)
(assert b8)
(push 1)
(assert (fp.gt (fp.mul RNE x (fp.add RNE y (fp #b0 #x7f #b00000000000000000001001))) (fp #b1 #x82 #b00000000000000000000000)))
; CHECK: Incremental profile cbp/backend: check=9 .*rebuild-inprobing=0
; CHECK: ^sat
(check-sat)
(pop 1)
(assert b9)
(push 1)
(assert (fp.eq (fp.add RNE y (fp #b0 #x7f #b00000000000000000001010)) (fp #b0 #x7f #b00000000000000000001010)))
; CHECK: Incremental profile cbp/backend: check=10 .*rebuild-inprobing=0
; CHECK: ^sat
(check-sat)
(pop 1)
(exit)
