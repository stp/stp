; Distinct remains a native source AST node through assertion storage, then
; receives pairwise semantics at the completed-root boundary.
; The model evaluator accepts the retained public handle after the solve.
;
; RUN: %solver --incremental=off %s | %OutputCheck --check-prefix=BATCH %s
; RUN: %solver --incremental=on %s | %OutputCheck --check-prefix=DRIVER %s
;
; BATCH: ^sat
; BATCH-NEXT: ^\($
; BATCH-NEXT: ^\(\(distinct x y z\) true\)$
; BATCH-NEXT: ^\)$
;
; DRIVER: ^sat
; DRIVER-NEXT: ^\($
; DRIVER-NEXT: ^\(\(distinct x y z\) true\)$
; DRIVER-NEXT: ^\)$
;
(set-logic QF_BV)
(set-option :produce-models true)
(declare-const x (_ BitVec 2))
(declare-const y (_ BitVec 2))
(declare-const z (_ BitVec 2))
(assert (distinct x y z))
(check-sat)
(get-value ((distinct x y z)))
