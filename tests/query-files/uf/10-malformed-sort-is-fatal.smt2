; RUN: not %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: not %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: argument 0 of f has sort Bool but the declaration requires \(_ BitVec 8\)
; CHECK-NOT: ^sat
; CHECK-NOT: REACHED-END
;
; The argument-sort half of 09-malformed-arity-is-fatal, and fatal for the
; same reason: recovering discarded the assertion the application sat in.
(set-logic QF_UFBV)
(declare-fun b () Bool)
(declare-fun f ((_ BitVec 8)) Bool)
(assert (f b))
(check-sat)
(echo "REACHED-END")
