; RUN: %solver --bb.simplify-during-bb=1 --bb.fp-native-arith=0 -d %s | %OutputCheck %s
; CHECK: ^sat$
;
; SymFPU's fp.rem unrolls past the bit-blaster's recursion budget, so the
; memos are primed. The divisor has two free bits, so many operands blast to
; constants and simplify_during_bb rewrites their parents. BBTerm memoised
; each result under the rewrite only, so the nodes asked for kept missing,
; each miss primed again, and the nesting grew by two frames per rewritten
; node. PrimeAudit aborted at 545 frames against a claim of 544. The node
; asked for is now memoised too.
(set-logic QF_FP)
(declare-const x Float64)
(declare-fun r () RoundingMode)
(declare-fun v () (_ BitVec 2))
(assert (not (fp.isSubnormal (fp.rem x ((_ to_fp 11 53) r (fp.roundToIntegral r ((_ to_fp 15 113) ((_ sign_extend 126) v))))))))
(check-sat)
