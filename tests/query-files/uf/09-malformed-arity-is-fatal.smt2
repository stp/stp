; RUN: not %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: not %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: f expects 1 argument but was applied to 2
; CHECK-NOT: ^sat
; CHECK-NOT: REACHED-END
;
; A malformed application ends the session. It used to be reported and then
; recovered from, which cost the assertion it appeared in: the command was
; discarded whole, the conjunct went with it, and the check-sat below answered
; the query that was left -- `sat` for a file STP had already said it could not
; read. STP answers (get-info :error-behavior) with immediate-exit, and this
; was one of the places that was untrue.
(set-logic QF_UFBV)
(declare-fun x () (_ BitVec 8))
(declare-fun f ((_ BitVec 8)) (_ BitVec 4))
(assert (= (f x x) #b0000))
(check-sat)
(echo "REACHED-END")
