; The driver-side twin of array-extensionality-tests/75: float cells
; quotient their bit patterns, so the pointwise eager instantiation is
; unsound for them and the round falls back to lemmas on demand -- with
; the batch pipeline's exact warning, not a blanket one -- and still
; decides correctly.
; RUN: %solver --incremental --array-equality --ackermanize %s 2>&1 | %OutputCheck %s
; CHECK-L: Warning: --ackermanize is disabled for queries with array equality over floating-point sorts.
; CHECK: ^unsat
(set-logic QF_ABVFP)
(declare-fun a () (Array (_ BitVec 2) (_ FloatingPoint 3 5)))
(declare-fun b () (Array (_ BitVec 2) (_ FloatingPoint 3 5)))
(declare-fun i () (_ BitVec 2))
(push 1)
(assert (= a b))
(assert (not (fp.eq (select a i) (select b i))))
(assert (not (fp.isNaN (select a i))))
(check-sat)
(pop 1)
