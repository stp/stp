; A distinct used as a Boolean UF actual is not in a monotone context. If the
; ordering pass replaced it with a strict chain, the actual would be forced
; true; this formula has a model only when that actual is false.
;
; RUN: %solver --uninterpreted-functions --incremental=off -s %s 2>&1 | %OutputCheck %s
;
; CHECK-NOT: Ordered
; CHECK: ^sat
;
(set-logic QF_UFBV)
(declare-fun g (Bool) Bool)
(declare-const x (_ BitVec 2))
(declare-const y (_ BitVec 2))
(declare-const z (_ BitVec 2))
(assert (not (g true)))
(assert (g (distinct x y z)))
(check-sat)
