; A rounding-mode actual must stay a rounding mode while a float operation
; over the application is blasted.
;
; Reading the value of (fp.sub r (f r) (f r)) blasts the subtraction with
; (f r) as an opaque operand. SymFPU's circuit asks which mode r is -- the
; sign of an exact zero depends on whether it is RTN -- and the simplifying
; factory, building an if-then-else on such a test, decides the tests in
; its branches by putting the constant in r's place. SymFPU's constants were
; plain five-bit bit-vectors, so that made (f r) an application of f to a
; bit-vector, and the factory refused to build it:
;
;   Fatal Error: UF_APPLY: uninterpreted functions: argument 0 of f has sort
;                (_ BitVec 5) but the declaration requires RoundingMode
;
; SymFPU's constants are now RoundingMode literals, and the factory only
; substitutes a constant of the term's own sort.
;
; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
;
; The term half of each pair is printed through get-value's letizing entry
; point, and STP keeps a subtraction as the addition of a negation.
;
; CHECK: ^sat
; x - x is +0 under every mode but RTN ...
; CHECK-L: ((fp.sub s (f s) (f s)) (fp #b0 #b00000000 #b00000000000000000000000))
; ... where it is -0.
; CHECK-L: ((fp.sub r (f r) (f r)) (fp #b1 #b00000000 #b00000000000000000000000))
; CHECK: REACHED-END
;
(set-option :produce-models true)
(set-logic QF_UFFP)
(declare-fun f (RoundingMode) (_ FloatingPoint 8 24))
(declare-const r RoundingMode)
(declare-const s RoundingMode)
(assert (= r RTN))
(assert (= s RNE))
(assert (= (f r) ((_ to_fp 8 24) RNE 1.0)))
(assert (= (f s) ((_ to_fp 8 24) RNE 2.0)))
(check-sat)
(get-value ((fp.sub s (f s) (f s))))
(get-value ((fp.sub r (f r) (f r))))
(echo "REACHED-END")
