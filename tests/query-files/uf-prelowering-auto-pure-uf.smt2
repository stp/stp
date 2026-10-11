; RUN: %solver --SMTLIB2 -s %s 2>&1 | %OutputCheck %s
; RUN: %solver --SMTLIB2 -s --uf-propagate-equalities=on %s 2>&1 | %OutputCheck --check-prefix=FORCED %s
;
; In pure QF_UF, AUTO skips the pre-lowering rewrite. An explicit ON still
; runs it on the same top-level equality.
; CHECK-NOT: UF: pre-lowering
; CHECK: ^sat$
; FORCED: UF: pre-lowering
; FORCED: ^sat$
(set-logic QF_UF)
(declare-sort S 0)
(declare-fun f (S) S)
(declare-fun a () S)
(declare-fun b () S)
(assert (= a b))
(assert (= (f a) (f b)))
(check-sat)
