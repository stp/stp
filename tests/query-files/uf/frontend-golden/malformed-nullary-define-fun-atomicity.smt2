; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK-NEXT: ^\(error ".*f expects 1 argument but was applied to 2"\)
; CHECK-NEXT: ^unsat
; CHECK-NEXT: ^"REACHED-END"
;
; The parameterless bit-vector define-fun is its own grammar action, distinct
; from the one with formals covered by malformed-define-fun-atomicity. A
; malformed application in its body used to leave the command latch set:
; define-fun printed success without consuming it, and the NEXT command's
; assertion consumed the stale latch and was silently dropped, so this file
; answered sat. The definition must register nothing, the diagnostic is
; nonfatal, and (assert false) must keep its effect.
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 4)) (_ BitVec 4))
(declare-const x (_ BitVec 4))
(define-fun bad () (_ BitVec 4) (f x x))
(assert false)
(check-sat)
(echo "REACHED-END")
