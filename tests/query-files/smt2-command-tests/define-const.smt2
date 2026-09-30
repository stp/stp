; RUN: %solver %s | %OutputCheck %s
(set-option :produce-models true)
(set-logic QF_AUFBVFP)
(declare-sort S 0)
(declare-const s S)
(define-const named-s S s)
(define-const b Bool true)
(define-const v (_ BitVec 8) #x2a)
(define-const f Float32 (_ +zero 8 24))
(define-const r RoundingMode RNE)
(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
(define-const aa (Array (_ BitVec 8) (_ BitVec 8)) (store a #x00 v))
(assert (and b (= v #x2a) (= s named-s) (fp.isZero f) (= r RNE)
             (= (select aa #x00) #x2a)))
; CHECK: ^sat$
(check-sat)
; CHECK: #x2A
(get-value (v))
(push 1)
(define-const local Bool false)
(assert local)
; CHECK: ^unsat$
(check-sat)
(pop 1)
(define-const local Bool true)
(assert local)
; CHECK: ^sat$
(check-sat)
(reset)
(set-logic QF_LRA)
(define-const rational Real (/ 1.0 3.0))
(assert (= (* 3.0 rational) 1.0))
; CHECK: ^sat$
(check-sat)
