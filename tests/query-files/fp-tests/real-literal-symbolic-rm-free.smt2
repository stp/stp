; RUN: %solver %s | %OutputCheck %s
;
; With the rounding mode left free, the conversion can still only take
; the values the five modes produce. 0.1 in Float16 has exactly two:
; 0x2e66 (RNE, RNA, RTN, RTZ) and 0x2e67 (RTP). Excluding both must be
; unsatisfiable -- there is no sixth rounding mode to escape through.
(set-logic QF_FP)
(declare-const r RoundingMode)
(declare-const x (_ FloatingPoint 5 11))
(assert (= x ((_ to_fp 5 11) r 0.1)))
(assert (distinct x (fp #b0 #b01011 #b1001100110)))
(assert (distinct x (fp #b0 #b01011 #b1001100111)))
; CHECK: ^unsat
(check-sat)
