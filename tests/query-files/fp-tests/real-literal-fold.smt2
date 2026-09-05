; RUN: %solver %s | %OutputCheck %s
;
; ((_ to_fp e s) rm <decimal>) folds to the same interned constant as the
; packed-bits spellings. The disjunction asks for any fold to disagree with
; its expected constant; unsat means every one landed exactly. (A
; conjunction of distincts would go unsat as soon as a single fold is
; right, hiding bugs in the rest.)
(set-logic QF_BVFP)
(declare-fun a () (_ FloatingPoint 8 24))
(declare-fun b () (_ FloatingPoint 8 24))
(declare-fun c () (_ FloatingPoint 8 24))
(declare-fun d () (_ FloatingPoint 11 53))
(assert (= a ((_ to_fp 8 24) RNE 1.5)))
(assert (= b ((_ to_fp 8 24) RNE 1.50)))
(assert (= c ((_ to_fp 8 24) RNE 2.0)))
(assert (= d ((_ to_fp 11 53) RNE 0.5)))
(assert (or
  (distinct a ((_ to_fp 8 24) #x3fc00000))
  (distinct a (fp #b0 #b01111111 #b10000000000000000000000))
  (distinct b ((_ to_fp 8 24) #x3fc00000))
  (distinct c ((_ to_fp 8 24) #x40000000))
  (distinct d (fp #b0 #b01111111110 #b0000000000000000000000000000000000000000000000000000))))
; CHECK: ^unsat
(check-sat)
