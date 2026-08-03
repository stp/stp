; RUN: %solver %s | %OutputCheck %s
;
; The floating-point names are keywords only inside the FP logics (SMT-LIB
; reserves theory symbols per-logic). In QF_BV they are ordinary symbols:
; inputs that predate floating-point support legitimately declare names
; like fp (a frame pointer), NaN or RNE, and must keep parsing.
(set-logic QF_BV)
(declare-fun fp () (_ BitVec 8))
(declare-fun NaN () (_ BitVec 8))
(declare-const RNE (_ BitVec 8))
(declare-fun to_fp () (_ BitVec 8))
(declare-fun fp.add () (_ BitVec 8))
(declare-fun Float32 () (_ BitVec 8))
(declare-fun +oo () (_ BitVec 8))
(declare-fun RoundingMode () (_ BitVec 8))
(declare-fun roundTowardZero () Bool)
(assert (= fp (bvadd NaN RNE)))
(assert (= to_fp (bvor fp.add Float32)))
(assert (= +oo RoundingMode))
(assert roundTowardZero)
; CHECK: ^sat
(check-sat)
