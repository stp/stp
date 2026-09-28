; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK-NEXT: ^unsat
; CHECK-NEXT: ^"REACHED-END"
;
; A define-fun formal is a binder, so it takes precedence over a global UF
; with the same spelling while both the formal list and body are parsed.
(set-logic QF_UFBV)
(declare-fun value ((_ BitVec 8)) (_ BitVec 8))
(define-fun identity ((value (_ BitVec 8))) (_ BitVec 8) value)
(assert (distinct (identity #x2a) #x2a))
(check-sat)
(echo "REACHED-END")
