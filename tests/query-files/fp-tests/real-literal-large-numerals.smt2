; RUN: %solver %s | %OutputCheck %s
;
; Numerals in a real literal are converted from their digits, so they are
; exact however large they are. Before, a numeral reached the fold as an
; unsigned that strtoul had wrapped: 2^32 + 1 arrived as 1, the 2^59
; denominator of a benchmark rational arrived as 0, and the fold either
; folded the wrong constant or refused a well-formed one.
;
; 2^1074, the denominator that names the smallest subnormal double, is
; past any fixed-width integer -- 324 digits -- and is the case that says
; the conversion reads digits rather than a machine number.
(set-logic QF_FP)
(declare-fun a () (_ FloatingPoint 11 53))
(declare-fun b () (_ FloatingPoint 11 53))
(declare-fun c () (_ FloatingPoint 11 53))
(declare-fun d () (_ FloatingPoint 11 53))
(declare-fun e () (_ FloatingPoint 11 53))
(assert (= a ((_ to_fp 11 53) RNE (/ 4294967297 1))))
(assert (= b ((_ to_fp 11 53) RNE 4294967297)))
(assert (= c ((_ to_fp 11 53) RNE (/ 45000000000000000 1))))
(assert (= d ((_ to_fp 11 53) RNE (/ 5764607523034235 576460752303423488))))
(assert (= e ((_ to_fp 11 53) RNE (/ 1 202402253307310618352495346718917307049556649764142118356901358027430339567995346891960383701437124495187077864316811911389808737385793476867013399940738509921517424276566361364466907742093216341239767678472745068562007483424692698618103355649159556340810056512358769552333414615230502532186327508646006263307707741093494784))))
(assert (or
  (distinct a ((_ to_fp 11 53) #x41f0000000100000))
  (distinct a b)
  (distinct c ((_ to_fp 11 53) #x4363fbe85edc9000))
  (distinct d ((_ to_fp 11 53) #x3f847ae147ae147b))
  (distinct e ((_ to_fp 11 53) #x0000000000000001))))
; CHECK: ^unsat
(check-sat)
