; An abstracted fp.to_sbv refined to a concrete value: the surrogate is
; pinned to 5 and a witness must exist, through the candidate check and
; the literal conversion evaluator (including its trap-free windows). The
; NaN operand variant exercises the unspecified-result row. Same answers
; exact, abstracted, and hosted by the incremental driver.
;
; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --fp-abstraction=true --fp-abstraction-ops=default,to_sbv,to_ubv -d %s | %OutputCheck %s
; CHECK: ^sat$
; CHECK: ^sat$
(set-logic QF_BVFP)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(declare-fun r () (_ BitVec 32))
(assert (= ((_ fp.to_sbv 32) roundTowardZero x) (_ bv5 32)))
(assert (fp.isNormal x))
(check-sat)
(assert (fp.isNaN y))
(assert (= r ((_ fp.to_sbv 32) roundNearestTiesToEven y)))
(check-sat)
(exit)
