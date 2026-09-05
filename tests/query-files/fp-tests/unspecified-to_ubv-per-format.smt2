; RUN: %solver %s | %OutputCheck %s
;
; The same per-sort freedom for fp.to_ubv, whose index carries the rounding
; mode as well as the operand: (_ FloatingPoint 8 24) and
; (_ FloatingPoint 11 21) both pack into 32 bits, so both applications built
; a 5 + 32 = 37 bit index and shared one array.
;
; #x7F000000 is 2^127 read as (8 24) and 2^1009 read as (11 21). Both are far
; out of range for an 8-bit unsigned result, so both results are unspecified,
; and independently so.
; CHECK: ^sat
(set-logic QF_BVFP)
(define-fun X () (_ FloatingPoint  8 24) ((_ to_fp  8 24) #x7F000000))
(define-fun Y () (_ FloatingPoint 11 21) ((_ to_fp 11 21) #x7F000000))
(assert (=        ((_ fp.to_ubv 8) RNE X) #x00))
(assert (distinct ((_ fp.to_ubv 8) RNE Y) #x00))
(check-sat)
