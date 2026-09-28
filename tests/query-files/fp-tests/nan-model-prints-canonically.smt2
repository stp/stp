; RUN: %solver %s | %OutputCheck %s
;
; A float pinned only to "is NaN" can take any of the many NaN bit patterns
; in the SAT model. The model printers spell every one of them as the one
; canonical quiet NaN -- positive, exponent all ones, only the quiet bit
; set -- so model text is deterministic at the value level rather than
; varying with the carrier bits the solver happened to pick, and matches
; what cvc5 and bitwuzla print for the same query. Covers the scalar
; get-value and get-model paths and a float-element array cell.
; (CHECK-L: these patterns hold regex metacharacters -- | -- so the plain
; CHECK form would match vacuously.)
(set-logic QF_ABVFP)
(set-option :produce-models true)
(declare-const x (_ FloatingPoint 8 24))
(declare-fun a () (Array (_ BitVec 2) (_ FloatingPoint 8 24)))
(assert (fp.isNaN x))
(assert (fp.isNaN (select a #b00)))
; CHECK: ^sat
(check-sat)
; CHECK-L: ( |x| (fp #b0 #b11111111 #b10000000000000000000000) )
(get-value (x))
; CHECK-L: (define-fun |x| () (_ FloatingPoint 8 24) (fp #b0 #b11111111 #b10000000000000000000000))
; CHECK-L: (define-fun |a| (_ BitVec 2) (_ FloatingPoint 8 24) #b00 (fp #b0 #b11111111 #b10000000000000000000000))
(get-model)
