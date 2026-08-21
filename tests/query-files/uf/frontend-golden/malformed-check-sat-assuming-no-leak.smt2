; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK-NEXT: ^\(error ".*f expects 1 argument but was applied to 2"\)
; CHECK-NEXT: ^unsat
; CHECK-NEXT: ^"REACHED-END"
;
; malformed-command-atomicity pins that a rejected check-sat-assuming prints
; no verdict. This pins the other half of the recovery: the rejection must not
; leak into the following command. A malformed assumption used to be consumed
; by the internal AddAssert, which dropped the poisoned assumption and left
; the latch for the NEXT assertion to consume, so (assert false) vanished and
; this file answered sat.
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 4)) (_ BitVec 4))
(declare-const x (_ BitVec 4))
(check-sat-assuming ((= (f x x) x)))
(assert false)
(check-sat)
(echo "REACHED-END")
