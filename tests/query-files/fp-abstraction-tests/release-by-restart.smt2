; RUN: %solver --fp-abstraction=true --fp-abstraction-values=0 --fp-abstraction-restart-width=64 -s %s 2>&1 | %OutputCheck %s
;
; A binary64 product pinned to a constant, one factor held in an interval
; whose ends are not factors of it, needs its value, and with no value
; lemmas allowed its first refutation releases it. With the restart width
; set, at this width the release runs the pipeline again with the product
; lowered exactly -- the ordinary lowering, with constant-bit propagation
; and the rest -- rather than splicing the multiplier into the running
; solver; the second run reports the run before it. The doubling is pinned
; by the power-of-two identity rule, so it is never refuted and stays
; abstracted throughout. (release-in-place-default.smt2 is the same query
; under the defaults, where the release is spliced.)
; CHECK: FpAbstraction: releasing 1 operation\(s\) exactly by running the pipeline again
; CHECK: 1 restarts
; CHECK: ^sat
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 11 53))
(declare-const y (_ FloatingPoint 11 53))
(assert (fp.lt ((_ to_fp 11 53) RNE 1.1) x))
(assert (fp.lt x ((_ to_fp 11 53) RNE 1.2)))
(assert (fp.isNormal y))
(assert (= (fp.mul RNE x y) ((_ to_fp 11 53) RNE 3.0)))
(assert (fp.isNormal (fp.mul RNE x ((_ to_fp 11 53) RNE 2.0))))
(check-sat)
