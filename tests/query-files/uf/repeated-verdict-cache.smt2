; A byte-identical repeated UF query is answered by the frontend verdict
; cache.  :check-sat-calls counts real solves, so it must remain one after
; both printed verdicts in every routing mode.
;
; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions %s 2>&1 | %OutputCheck %s
; CHECK-NEXT: ^unsat
; CHECK-NEXT: ^\(:check-sat-calls 1$
; CHECK: ^unsat
; CHECK-NEXT: ^\(:check-sat-calls 1$
;
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (= x y))
(assert (distinct (f x) (f y)))
(check-sat)
(get-info :all-statistics)
(check-sat)
(get-info :all-statistics)
