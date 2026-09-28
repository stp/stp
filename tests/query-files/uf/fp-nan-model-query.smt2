; The seam option A creates, and the one place in the floating-point work
; where getting it wrong is quiet rather than loud.
;
; The checker observed the canonically-packed actual, because the name it
; read is defined as FP_TO_IEEE_BV of the argument. A model query about an
; application the solve never reached is answered from that same certified
; seed, keyed on actuals the counterexample walk evaluates -- and those come
; back as raw carriers out of the SAT assignment, with whatever NaN payload
; the solver happened to pick. Keying the seed with the raw carrier would
; miss the case and fall through to the default, so model evaluation would
; disagree with the interpretation the define-fun printed. Nothing aborts to
; say so: both answers are well-sorted.
;
; f(fp.abs x) is the query that reaches it. x is NaN, so fp.abs x is the same
; *value* and congruence requires the same result -- but it is a distinct
; durable node the solve never reached, and its evaluated carrier need not be
; the one the seed was keyed on.
;
; The literal rows below test something weaker but worth keeping: every NaN
; pattern interns as the one canonical quiet NaN at construction
; (STPMgr::CreateFPConst), so two spellings are one node before the UF
; machinery ever sees them. Both echo back as that canonical literal.
;
; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: ^sat
; CHECK-L: ( (|f| |x|)  #x3 )
; CHECK-L: ( (=  #x3 (|f| (fp.abs |x|))) true )
; CHECK-L: ( (=  #x3 (|f| (fp #b0 #b11111111 #b10000000000000000000000))) true )
; CHECK-L: ( (=  #x3 (|f| (fp #b0 #b11111111 #b10000000000000000000000))) true )
; A non-NaN actual is a different value and carries no such obligation, so it
; resolves through the default instead. It must still be answerable.
; CHECK-L: ( (bvadd  #x1 (|f| (fp #b0 #b10000000 #b00000000000000000000000)))
; CHECK: REACHED-END
;
(set-option :produce-models true)
(set-logic QF_UFBVFP)
(declare-fun f ((_ FloatingPoint 8 24)) (_ BitVec 4))
(declare-const x (_ FloatingPoint 8 24))
(assert (fp.isNaN x))
(assert (= (f x) #x3))
(check-sat)
(get-value ((f x)))
(get-value ((= (f (fp.abs x)) #x3)))
(get-value ((= (f (fp #b0 #b11111111 #b00000000000000000000001)) #x3)))
(get-value ((= (f (fp #b1 #b11111111 #b11000000000000000000000)) #x3)))
(get-value ((bvadd (f (fp #b0 #b10000000 #b00000000000000000000000)) #x1)))
(echo "REACHED-END")
