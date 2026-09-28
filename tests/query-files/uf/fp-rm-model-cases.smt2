; A generated define-fun with floating-point and rounding-mode values in its
; *conditions*, not just in its result.
;
; fp-model-values.smt2 pins a float codomain, where the values printed are
; the ite branches. This pins the other half: the case conditions are
; (= x0 <value>) over the declared domain sorts, so a float there has to
; print in (fp ...) syntax and a rounding mode by name, or the define-fun is
; not a legal SMT-LIB term however correct the interpretation behind it is.
;
; --check-sanity replays the certified interpretation against the raw stack,
; so the text below and the model that satisfied the assertions cannot
; quietly differ.
;
; RUN: %solver --uninterpreted-functions --check-sanity --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --check-sanity --incremental=on %s 2>&1 | %OutputCheck %s
;
; CHECK: ^sat
; Both cases land on one line, so they are pinned as one literal -- which
; also pins the nesting and the else branch.
; CHECK-L: (define-fun |f| ((x0 (_ FloatingPoint 8 24)) (x1 RoundingMode)) (_ BitVec 4)
; CHECK-L: (ite (and (= x0 (fp #b0 #b10000000 #b00000000000000000000000)) (= x1 RNE))  #x1 (ite (and (= x0 (fp #b1 #b10000001 #b01000000000000000000000)) (= x1 RTZ))  #x2  #x0)))
; CHECK: REACHED-END
;
(set-logic QF_UFBVFP)
(set-option :produce-models true)
(declare-fun f ((_ FloatingPoint 8 24) RoundingMode) (_ BitVec 4))
(declare-const u (_ FloatingPoint 8 24))
(declare-const v (_ FloatingPoint 8 24))
(assert (= u (fp #b0 #b10000000 #b00000000000000000000000)))
(assert (= v (fp #b1 #b10000001 #b01000000000000000000000)))
(assert (= (f u RNE) #x1))
(assert (= (f v RTZ) #x2))
(check-sat)
(get-model)
(echo "REACHED-END")
