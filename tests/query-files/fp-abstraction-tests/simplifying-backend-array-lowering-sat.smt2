; REQUIRES: minisat
; RUN: %solver -d --fp-abstraction=1 --fp-abstraction-ops=all --simplifying-minisat --array-equality %s | %OutputCheck %s
; CHECK: ^sat
; As simplifying-backend-sat, where the model checked by -d is the first
; to notice: a lemma spliced over an eliminated proxy surfaced as "an
; array equality's lowering is false in the model, but the model gives
; the two operands the user equated identical contents".
(set-logic QF_ABVFP)
(declare-const x2 (Array (_ BitVec 13) Float128))
(declare-const x Float128)
(declare-const x9 Bool)
(declare-fun a () (Array Float128 (_ BitVec 5)))
(assert (not (ite x9 (distinct x2 (store x2 ((_ zero_extend 9) ((_ fp.to_ubv 4) roundNearestTiesToAway (fp.add roundTowardPositive x (fp (_ bv0 1) (_ bv0 15) (_ bv0 112))))) (select x2 (_ bv0 13)))) (distinct (store a (select x2 (_ bv0 13)) (_ bv16 5)) (store a (select x2 (_ bv0 13)) ((_ extract 5 1) ((_ fp.to_ubv 6) RNE ((_ to_fp_unsigned 11 53) roundTowardZero (_ bv33 7)))))))))
(check-sat)
