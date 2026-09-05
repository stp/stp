; RUN: %solver %s | %OutputCheck %s
;
; The rational spelling (/ p q): 1/3 is inexact and mode-sensitive, 2/4
; is exactly 0.5, decimal components only shift powers of ten between the
; sides ((/ 1.2 3.25) is (/ 24 65)), the two negative spellings agree,
; (/ 7 1) is the bare numeral 7, and (/ 0 9) is the (unsigned) real zero.
(set-logic QF_FP)
(declare-fun a () (_ FloatingPoint 8 24))
(declare-fun b () (_ FloatingPoint 8 24))
(declare-fun c () (_ FloatingPoint 8 24))
(declare-fun d () (_ FloatingPoint 11 53))
(declare-fun e () (_ FloatingPoint 8 24))
(declare-fun f () (_ FloatingPoint 8 24))
(declare-fun g () (_ FloatingPoint 8 24))
(assert (= a ((_ to_fp 8 24) RNE (/ 1 3))))
(assert (= b ((_ to_fp 8 24) RTZ (/ 1 3))))
(assert (= c ((_ to_fp 8 24) RNE (/ 2 4))))
(assert (= d ((_ to_fp 11 53) RNE (/ 1.2 3.25))))
(assert (= e ((_ to_fp 8 24) RNE (/ (- 1) 3))))
(assert (= f ((_ to_fp 8 24) RNE (- (/ 1 3)))))
(assert (= g ((_ to_fp 8 24) RNE (/ 7 1))))
(assert (or
  (distinct a ((_ to_fp 8 24) #x3eaaaaab))
  (distinct b ((_ to_fp 8 24) #x3eaaaaaa))
  (distinct c ((_ to_fp 8 24) #x3f000000))
  (distinct d ((_ to_fp 11 53) RNE (/ 24 65)))
  (distinct e f)
  (distinct e ((_ to_fp 8 24) #xbeaaaaab))
  (distinct g ((_ to_fp 8 24) RNE 7))
  (distinct ((_ to_fp 8 24) RNE (/ 0 9)) (_ +zero 8 24))))
; CHECK: ^unsat
(check-sat)
