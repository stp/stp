; RUN: %solver -d %s | %OutputCheck %s
;
; Regression: the same counterexample re-evaluation (-d) over a floating-point
; *value* operation that survives bit-blasting. The model evaluator strips the
; format off every operand; re-blasting fp.sqrt / a conversion / fp.max over
; those bare bit-vectors dropped the operand format and aborted (a 0/0-format
; decode / CreateBVConst-of-width-0). fp.to_sbv feeds fp.to_fp_unsigned into
; fp.max under fp.isPositive, kept live by the ite.
(set-logic QF_BVFP)
(declare-fun x4 () Float32)
(declare-fun x5 () RoundingMode)
(declare-fun x0 () (_ BitVec 23))
(declare-fun x2 () (_ BitVec 32))
(assert (bvsge x2 x2))
(assert (=> (bvsge x2 x2)
  (fp.isPositive (fp.max
    ((_ to_fp_unsigned 8 24)
       (ite (= (bvult x0 x0) (fp.isSubnormal (fp.sqrt RNA x4))) RNA x5)
       ((_ fp.to_sbv 63) x5 x4))
    ((_ to_fp_unsigned 8 24)
       (ite (= (bvult x0 x0) (fp.isSubnormal (fp.sqrt RNA x4))) RNA x5)
       ((_ fp.to_sbv 63) x5 x4))))))
; CHECK: ^sat
(check-sat)
