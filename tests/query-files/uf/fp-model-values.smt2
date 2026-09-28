; A floating-point UF result is published in floating-point syntax, at the
; declared sort, not as the packed bit-vector the checker actually stores.
; The generated define-fun has to be a legal SMT-LIB term: its signature
; names (_ FloatingPoint 8 24) and every value in it is an (fp ...).
;
; --check-sanity replays the certified interpretation against the raw stack,
; so the printed model and the model used to satisfy the assertions cannot
; quietly differ.
;
; RUN: %solver --uninterpreted-functions --check-sanity --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --check-sanity --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: ^sat
; CHECK-L: define-fun |q| ((x0 (_ BitVec 4))) (_ FloatingPoint 8 24)
; CHECK-L: (fp #b0 #b10000000 #b10000000000000000000000)
; CHECK-L: ( (|q| |i|) (fp #b0 #b10000000 #b10000000000000000000000) )
; CHECK-L: ( (|w| |z|)  #x01 )
; CHECK: REACHED-END
;
(set-option :produce-models true)
(set-logic QF_UFBVFP)
(declare-fun q ((_ BitVec 4)) (_ FloatingPoint 8 24))
(declare-fun w ((_ FloatingPoint 8 24)) (_ BitVec 8))
(declare-const i (_ BitVec 4))
(declare-const z (_ FloatingPoint 8 24))
(assert (= i #x1))
(assert (= (q i) (fp #b0 #b10000000 #b10000000000000000000000)))
(assert (= (w z) #x01))
(check-sat)
(get-model)
(get-value ((q i)))
(get-value ((w z)))
(echo "REACHED-END")
