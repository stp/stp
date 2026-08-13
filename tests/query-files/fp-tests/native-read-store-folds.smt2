; RUN: %solver --array-equality %s | %OutputCheck %s
; RUN: %solver --array-equality --disable-simplifications %s | %OutputCheck %s
; RUN: %solver --array-equality --bb.fp-native-cmp=false %s | %OutputCheck %s
;
; Regression test for https://github.com/stp/stp/issues/824.
;
; The store index is a same-format to_fp of the read index, so lowering
; collapses the two and the simplifying factory folds the read-over-store
; to the stored value -- an encode() circuit for the fp.roundToIntegral,
; not a read. The native comparison gate must notice the fold and send the
; predicate to SymFPU rather than consume the circuit as if it carried a
; float sort (it used to abort with std::length_error in BBfpIsNaN).
;
; CHECK: ^sat
(set-logic QF_ABVFP)
(declare-const _x0 (_ FloatingPoint 11 53))
(declare-const _x2 (Array (_ FloatingPoint 11 53) (_ FloatingPoint 15 113)))
(assert (let ((_let0 (select _x2 _x0)))
  (let ((_let1 (fp.roundToIntegral RNA _let0)))
  (let ((_let2 ((_ to_fp 11 53) RNA _x0)))
    (=> (fp.gt (select (store _x2 _let2 _let1) _x0) _let0)
        (distinct (store _x2 _let2 _let0) (store _x2 _x0 _let1)))))))
(check-sat)
(exit)
