; RUN: %solver %s | %OutputCheck %s
;
; Negated real constants: (- 1.5) is the exact negative, negation swaps
; the directed modes (-0.1 in Float16 rounds up in magnitude only under
; RTN where 0.1 does only under RTP), negative overflow is mode-specific
; toward -oo or the most-negative finite, and (- 0.0) is the real zero,
; which has no sign: it converts to +zero, not -zero.
(set-logic QF_FP)
(declare-fun a () (_ FloatingPoint 8 24))
(declare-fun b () (_ FloatingPoint 5 11))
(declare-fun c () (_ FloatingPoint 5 11))
(declare-fun d () (_ FloatingPoint 5 11))
(declare-fun e () (_ FloatingPoint 5 11))
(declare-fun f () (_ FloatingPoint 8 24))
(assert (= a ((_ to_fp 8 24) RNE (- 1.5))))
(assert (= b ((_ to_fp 5 11) RTN (- 0.1))))
(assert (= c ((_ to_fp 5 11) RTP (- 0.1))))
(assert (= d ((_ to_fp 5 11) RTN (- 65520.0))))
(assert (= e ((_ to_fp 5 11) RTZ (- 65520.0))))
(assert (= f ((_ to_fp 8 24) RTN (- 0.0))))
(assert (or
  (distinct a ((_ to_fp 8 24) #xbfc00000))
  (distinct b (fp #b1 #b01011 #b1001100111))
  (distinct c (fp #b1 #b01011 #b1001100110))
  (distinct d (_ -oo 5 11))
  (distinct e (fp #b1 #b11110 #b1111111111))
  (distinct f (_ +zero 8 24))))
; CHECK: ^unsat
(check-sat)
