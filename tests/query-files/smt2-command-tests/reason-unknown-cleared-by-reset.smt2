; Reset invalidates the previous unknown result. Both drivers must refuse
; reason-unknown until another check returns unknown.
; RUN: not %solver --incremental=off --max-time=0 %s | %OutputCheck %s
; RUN: not %solver --incremental=on --max-time=0 %s | %OutputCheck %s
;
; CHECK: ^unknown$
; CHECK-NEXT: ^\(:reason-unknown timeout\)$
; CHECK-NEXT: ^\(error "get-info :reason-unknown requires a preceding unknown result"\)$
;
(set-logic QF_BV)
(declare-fun a () (_ BitVec 32))
(declare-fun b () (_ BitVec 32))
(assert (= (bvmul ((_ zero_extend 32) a) ((_ zero_extend 32) b)) #x7ffffffc80000005))
(assert (bvugt a #x00000001))
(assert (bvugt b #x00000001))
(check-sat)
(get-info :reason-unknown)
(reset)
(get-info :reason-unknown)
