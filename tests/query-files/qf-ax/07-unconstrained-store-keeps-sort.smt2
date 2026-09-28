; An unconstrained store or array if-then-else over a declared-sort array is
; replaced by a fresh array. The fresh array must have the declared sort, or
; the array equality rebuilt around it has operands of different sorts.
;
; RUN: %solver -d %s | %OutputCheck %s
; CHECK: ^sat
; CHECK-NEXT: ^sat
(set-logic QF_AX)
(declare-sort I 0)
(declare-sort E 0)
(declare-fun v () (Array I E))
(declare-fun w () (Array I E))
(declare-fun u () (Array I E))
(declare-fun i () I)
(declare-fun e () E)
(declare-fun b () Bool)
(push 1)
(assert (not (= v (store w i e))))
(check-sat)
(pop 1)
(assert (not (= v (ite b w u))))
(check-sat)
