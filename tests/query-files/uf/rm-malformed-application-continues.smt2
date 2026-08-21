; A malformed application of a RoundingMode-returning function is rejected
; nonfatally, exactly as 09-malformed-arity-continues.smt2 pins for a
; bit-vector one, and the session carries on to answer the rest.
;
; The enclosing (= ...) reduces before the rejected command is discarded, and
; it sort-checks its operands. So the placeholder the parser substitutes has
; to be a term of the declared sort: a bare five-bit zero has the right
; carrier width and the wrong sort, and turns this into a fatal syntax error.
;
; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: k expects 1 argument but was applied to 2
; CHECK: argument 0 of f has sort \(_ BitVec 4\) but the declaration requires RoundingMode
; CHECK-NOT: operands of the same sort
; CHECK: ^sat
; CHECK: REACHED-END
;
(set-logic QF_UFBVFP)
(declare-fun k ((_ BitVec 4)) RoundingMode)
(declare-fun f (RoundingMode) (_ BitVec 4))
(assert (= (k #x0 #x1) RNE))
(assert (= (f #x0) #x2))
(assert (= (k #x0) RTZ))
(check-sat)
(echo "REACHED-END")
