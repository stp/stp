; RUN: %solver %s | %OutputCheck %s
;
; The *LRA logics are the FP logics plus a theory of reals. The benchmarks
; in them use a real only as the literal argument of to_fp, which is the
; one real term this grammar has, so the names are accepted and the
; floating-point keywords they imply are enabled.
(set-logic QF_BVFPLRA)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun v () (_ BitVec 32))
(assert (= x ((_ to_fp 8 24) RNE (/ 1 2))))
(assert (= v ((_ fp.to_sbv 32) RTZ x)))
; CHECK: ^sat
(check-sat)
