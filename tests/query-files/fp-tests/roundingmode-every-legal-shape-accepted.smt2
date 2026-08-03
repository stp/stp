; RUN: %solver %s | %OutputCheck %s
;
; The companion to roundingmode-must-be-a-mode-not-5-bits.smt2. Tightening
; the check from the carrier's width to the sort must not turn away anything
; that does denote a mode, and RoundingMode has no width of its own to test,
; so the predicate has to know every shape one can arrive in: a literal, a
; declared variable, a read from a RoundingMode-element array, and an ite
; over those.
;
; One operation per shape, so a predicate that forgot any of them fails here
; rather than in some corner of the corpus.
; CHECK: ^sat
(set-logic QF_ABVFP)
(declare-const r RoundingMode)
(declare-const c Bool)
(declare-const modes (Array (_ BitVec 2) RoundingMode))
(declare-const x (_ FloatingPoint 8 24))
(assert (fp.isNormal x))
(assert (fp.isNormal (fp.add RNE x x)))
(assert (fp.isNormal (fp.mul r x x)))
(assert (fp.isNormal (fp.div (ite c RTZ r) x x)))
(assert (fp.isNormal (fp.sqrt (select modes #b01) (fp.abs x))))
(assert (fp.isNormal (fp.roundToIntegral (ite c (select modes #b00) RTP) x)))
(assert (= ((_ fp.to_ubv 8) r x) #x01))
(assert (fp.isNormal ((_ to_fp 8 24) (select modes #b11) x)))
(check-sat)
