; What declare-sort still refuses, and what it does with scope.
;
; A parametric sort has no reading as a finite carrier and stays unsupported.
; The name follows assertion-frame scope like every other declaration, so a
; sort declared inside a push is gone after the matching pop and using it is
; the ordinary unknown-sort error -- which is fatal, so it comes last.
;
; RUN: not %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: not %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: ^unsupported
; CHECK: ^sat
; CHECK: SCOPE-CLOSED
; CHECK: not built in, and not a declared sort
;
(set-logic QF_UFBV)
(declare-sort Pair 1)
(push 1)
(declare-sort Scoped 0)
(declare-fun a () Scoped)
(declare-fun b () Scoped)
(assert (distinct a b))
(check-sat)
(pop 1)
(echo "SCOPE-CLOSED")
(declare-fun c () Scoped)
