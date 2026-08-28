; RUN: not %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: not %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK-NEXT: ^\(error ".*f expects 1 argument but was applied to 2"\)
; CHECK-NOT: ^unsat
; CHECK-NOT: ^"REACHED-END"
;
; A refused define-fun stores neither a body nor its temporary formal, and
; nothing after it runs. The (assert false) is kept so that a regression which
; resumed the session would have to answer it.
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(define-fun malformed ((x (_ BitVec 8))) (_ BitVec 8) (f x x))
(assert false)
(check-sat)
(echo "REACHED-END")
