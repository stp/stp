; RUN: %solver %s | %OutputCheck %s
; Reduced from a fuzzer-generated QF_ABV file. The sharing-aware rewriting
; pass pushed a constant BVAND through an ITE-of-constants without checking
; the BVAND's arity, dropping its remaining operands: here
; (bvor 301 (zero_extend e) srem) collapsed to the constant 301, and in debug
; builds the bogus SAT model then failed the model check and aborted on
; "Assertion `arrayops' failed".
(set-logic QF_BV)
(declare-fun v198057 () (_ BitVec 14))
(declare-fun v198060 () (_ BitVec 14))
(assert
 (let ((e198068 (ite (bvsaddo (_ bv0 14) v198060) (_ bv1 1) (_ bv0 1))))
 (let ((e198074 (ite (= v198057 ((_ zero_extend 13) e198068)) (_ bv1 1) (_ bv0 1))))
 (let ((e198085 (bvsrem ((_ sign_extend 13) e198074) v198057)))
 (let ((e198095 (bvor (_ bv301 14) ((_ zero_extend 13) e198074) e198085)))
 (not (= e198095 e198085)))))))
; CHECK-NEXT: ^sat
(check-sat)
(exit)
