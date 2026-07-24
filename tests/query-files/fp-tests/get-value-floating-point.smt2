; RUN: %solver %s | %OutputCheck %s
;
; Model output for a floating-point variable must use fp syntax
; (fp #bSign #bExp #bSig), not the raw packed bit-vector. get-model was already
; correct; this guards get-value, which used to print the value as a bitvector
; literal (e.g. #x30) -- a value of the wrong sort. Values are pinned bit-for-bit
; with SMT '=' so the model, and hence the output, is deterministic.
(set-logic QF_FP)
(set-option :produce-models true)
(declare-fun x () (_ FloatingPoint 3 5))
(declare-fun y () (_ FloatingPoint 3 5))
(assert (= x (fp #b0 #b011 #b0000)))
(assert (= y (fp #b1 #b010 #b0110)))
; CHECK: sat
(check-sat)
; get-model prints x in fp syntax, with its sort. (CHECK-L: these patterns
; hold regex metacharacters -- |, ( -- so the plain CHECK form would match
; vacuously.)
; CHECK-L: define-fun |x| () (_ FloatingPoint 3 5) (fp #b0 #b011 #b0000)
(get-model)
; get-value prints in the requested order, both in fp syntax (not #x..)
; CHECK-L: |x| (fp #b0 #b011 #b0000)
; CHECK-L: |y| (fp #b1 #b010 #b0110)
(get-value (x y))
