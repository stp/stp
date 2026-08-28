; RUN: not %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: not %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK-NEXT: ^\(error ".*f expects 1 argument but was applied to 2"\)
; CHECK-NOT: ^unsat
; CHECK-NOT: ^"REACHED-END"
;
; The parameterless bit-vector define-fun is its own grammar action, distinct
; from the one with formals that malformed-define-fun-atomicity covers, and it
; is refused in the same place. While these recovered, this action was where a
; malformed body left the command latch set: define-fun printed success
; without consuming it, the NEXT command's assertion consumed the stale latch
; and was silently dropped, and the file answered sat.
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 4)) (_ BitVec 4))
(declare-const x (_ BitVec 4))
(define-fun bad () (_ BitVec 4) (f x x))
(assert false)
(check-sat)
(echo "REACHED-END")
