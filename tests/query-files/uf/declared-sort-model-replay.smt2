; A model defines the current signature and qualifies every abstract value.
; Domain-only sorts still appear in function signatures, quoted sort names
; remain quoted, and the reserved @ namespace cannot collide with S!0.
; RUN: %solver --uninterpreted-functions --incremental=off -p %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on -p %s 2>&1 | %OutputCheck %s
; CHECK: ^sat
; CHECK: ^\(define-fun \|h\| \(\(x0 S\)\) Bool$
; CHECK: SIGNATURE-ONLY-DONE
; CHECK: ^\(define-fun \|[ab]\| \(\) \|my sort\| \(as \|@my sort![0-9]+\| \|my sort\|\)\)$
; CHECK: QUOTED-DONE
; CHECK: ^\(define-fun \|S!0\| \(\) S \(as \|@S![0-9]+\| S\)\)$
;
(set-logic QF_UFBV)
(declare-sort S 0)
(declare-fun h (S) Bool)
(declare-fun z () (_ BitVec 4))
(assert (= z #x1))
(check-sat)
(get-model)
(echo "SIGNATURE-ONLY-DONE")
(reset)
(set-logic QF_UFBV)
(declare-sort |my sort| 0)
(declare-fun a () |my sort|)
(declare-fun b () |my sort|)
(assert (distinct a b))
(check-sat)
(get-model)
(echo "QUOTED-DONE")
(reset)
(set-logic QF_UFBV)
(declare-sort S 0)
(declare-fun |S!0| () S)
(declare-fun b () S)
(assert (distinct |S!0| b))
(check-sat)
(get-model)
