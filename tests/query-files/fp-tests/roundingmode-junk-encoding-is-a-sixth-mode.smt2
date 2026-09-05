; RUN: not %solver %s 2>&1 | %OutputCheck %s
;
; A rounding mode is carried as a 5-bit bitvector, and every operation that
; takes one used to check exactly that: "is it 5 bits wide". SMT-LIB's
; RoundingMode has five values; the carrier has thirty-two. The check is now
; the sort -- STPMgr::isRoundingModeSortedTerm.
;
; Why that has to be the sort and not the width: an encoding matching none of
; the five is not merely "some mode", it is a behaviour no standard has.
;
; With every equality in symfpu's roundingDecision false (rounder.h:149-155)
; nothing ever rounds up, so it truncates and overflows to max, as RTZ does.
; But makeRoundingResult's returnZero (rounder.h:113-117) lists RTZ, so RTZ
; flushes an underflow to zero -- and with all five equalities false that is
; false too, giving the minimum subnormal instead, which is RTP's answer.
;
; Truncating rules out RTP; underflowing to the minimum rules out RTZ. So the
; two assertions below hold together under no legal rounding mode, and this
; file was answered *sat* when r was allowed to be a bare 5-bit bitvector.
; Substituting each of RNE/RNA/RTP/RTN/RTZ for r gives unsat five times over.
;
; Refused at the front door now, so the sixth behaviour is unreachable rather
; than merely unlikely. Kept as the reason the refusal is not pedantry.
; CHECK: expected a rounding mode
(set-logic QF_BVFP)
(declare-const r (_ BitVec 5))
(assert (distinct r #b00001)) (assert (distinct r #b00010))
(assert (distinct r #b00100)) (assert (distinct r #b01000))
(assert (distinct r #b10000))

(define-fun tiny  () (_ FloatingPoint 8 24) (fp #b0 #b00011011 #b00000000000000000000000)) ; 2^-100
(define-fun one   () (_ FloatingPoint 8 24) (fp #b0 #b01111111 #b00000000000000000000000)) ; 1.0
(define-fun three () (_ FloatingPoint 8 24) (fp #b0 #b10000000 #b10000000000000000000000)) ; 3.0

; 2^-200 underflows: only RTP (of the five, at this sign) gives a subnormal.
(assert (fp.isSubnormal (fp.mul r tiny tiny)))
; 1/3 is inexact, and truncating puts it strictly below RTP's answer.
(assert (fp.lt (fp.div r one three) (fp.div RTP one three)))
(check-sat)
