; A malformed application of a RoundingMode-returning function is refused
; exactly as 09-malformed-arity-is-fatal pins for a bit-vector one, and so is
; an argument offered to a RoundingMode-sorted parameter.
;
; RoundingMode is carried as a five-bit one-hot bit-vector, so these two are
; the pair most at risk of being compared by carrier width rather than by
; sort. Both must be refused at the application, before any enclosing
; production gets to sort-check anything.
;
; RUN: not %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: not %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; RUN: not %solver --uninterpreted-functions %S/Inputs/rm-malformed-argument-sort.smt2 2>&1 | %OutputCheck --check-prefix=ARGSORT %s
; CHECK: k expects 1 argument but was applied to 2
; CHECK-NOT: operands of the same sort
; CHECK-NOT: ^sat
; CHECK-NOT: REACHED-END
;
; ARGSORT: argument 0 of f has sort \(_ BitVec 4\) but the declaration requires RoundingMode
; ARGSORT-NOT: operands of the same sort
; ARGSORT-NOT: ^sat
;
; One case per input: refusing ends the run, so the second cannot be reached
; from the first.
(set-logic QF_UFBVFP)
(declare-fun k ((_ BitVec 4)) RoundingMode)
(assert (= (k #x0 #x1) RNE))
(check-sat)
(echo "REACHED-END")
