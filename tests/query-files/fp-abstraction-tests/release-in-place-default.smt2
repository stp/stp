; RUN: %solver --fp-abstraction=true --fp-abstraction-values=0 -s %s 2>&1 | %OutputCheck %s
;
; The query of release-by-restart.smt2 under the defaults: the release of
; the pinned product is spliced into the running solver, not made by
; running the pipeline again. A restart exists so that the bit-vector
; abstraction can see the released circuit, and without that abstraction
; it loses more than it wins, so --fp-abstraction-restart-width is 0 unless
; --bv-term-abstraction is on. One run, one release, no restart.
; CHECK-NOT: running the pipeline again
; CHECK: FpAbstraction: 1 abstracted .* 1 releases, .* 0 restarts
; CHECK: ^sat
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 11 53))
(declare-const y (_ FloatingPoint 11 53))
(assert (fp.lt ((_ to_fp 11 53) RNE 1.1) x))
(assert (fp.lt x ((_ to_fp 11 53) RNE 1.2)))
(assert (fp.isNormal y))
(assert (= (fp.mul RNE x y) ((_ to_fp 11 53) RNE 3.0)))
(check-sat)
