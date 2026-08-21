; Formats other than Float32, and a floating-point result crossing the array
; boundary.
;
; Every other floating-point row in this directory is (_ FloatingPoint 8 24),
; so nothing would notice a lowering that had 32 baked into it somewhere. The
; packed carrier is eb + sb, which is 64 for a double and 8 for the small
; format below -- and the small one is not an interchange width at all, which
; is the point of testing it.
;
; RUN: %solver --uninterpreted-functions --check-sanity --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --check-sanity --incremental=on %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --uf-ackermann=on --incremental=off %s 2>&1 | %OutputCheck %s
;
; CHECK: ^unsat
; CHECK: ^unsat
; CHECK: ^unsat
; CHECK: ^sat
; CHECK: ^sat
; CHECK-L: ( (|d| |i|) (fp #b0 #b01111111111 #b1000000000000000000000000000000000000000000000000000) )
; CHECK: REACHED-END
;
(set-logic QF_UFABVFP)
(set-option :produce-models true)
(declare-fun d ((_ BitVec 4)) (_ FloatingPoint 11 53))
(declare-fun h ((_ BitVec 4)) (_ FloatingPoint 3 5))
(declare-fun g ((_ FloatingPoint 3 5)) (_ BitVec 4))
(declare-const i (_ BitVec 4))
(declare-const j (_ BitVec 4))
(push 1)
; A double codomain.
(assert (= i j))
(assert (not (= (d i) (d j))))
(check-sat)
(pop 1)
(push 1)
; A format that is not an IEEE interchange width.
(assert (= i j))
(assert (not (= (h i) (h j))))
(check-sat)
(pop 1)
(push 1)
; Two NaN literals of that small format, as constant actuals: one value, so
; the two applications are congruent.
(assert (distinct (g (fp #b0 #b111 #b0001)) (g (fp #b1 #b111 #b1000))))
(check-sat)
(pop 1)
(push 1)
; A float result stored into and read back out of a float-element array.
(declare-const a (Array (_ BitVec 4) (_ FloatingPoint 11 53)))
(assert (= i j))
(assert (= (select (store a i (d i)) i) (d j)))
(check-sat)
(pop 1)
(push 1)
; And a double read back through the model.
(assert (= (d i) ((_ to_fp 11 53) RNE 1.5)))
(check-sat)
(get-value ((d i)))
(pop 1)
(echo "REACHED-END")
