; Float blasting must not lower a UF application's actual.
;
; Reading a model value for a float-valued term runs the float blaster over
; that term, and the blaster's generic rebuild substitutes each lowered child
; into the node it is rebuilding. Under a UF application that is wrong twice
; over: an application's actuals are stated in source sorts and the UF layer
; both validates and compares them there, so replacing a float actual with the
; bits it lowered to changes what the application denotes -- and the node
; factory refuses to build it at all, which took the process down with
;
;   Fatal Error: UF_APPLY: uninterpreted functions: argument 0 of f has sort
;                (_ BitVec 32) but the declaration requires (_ FloatingPoint 8 24)
;
; The application already *is* the bits of its result -- UFContext::apply
; builds it at the codomain's packed width -- so there was nothing to gain by
; descending into one either. The blaster now treats an application as an
; opaque carrier, exactly as it treats a float symbol or an array read, and
; leaves its actuals to whoever resolves the application: the UF lowering pass
; before a solve, the counterexample walk's UF_APPLY arm after one.
;
; It takes a *computed* actual to reach this. A symbol or a constant lowers to
; itself, so the rebuild never fired and the application came back untouched:
; the first two rows are those cases, kept so a fix cannot quietly change
; them. The rest are the defect, under each of the three codomain kinds a
; declaration can have.
;
; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
;
; The term half of each pair is printed through get-value's letizing entry
; point, so the computed actual -- named once as the operand and again inside
; the application -- comes back as a let binding rather than twice over.
;
; CHECK: ^sat
; x is -3, so fp.abs x is 3, f(3) is 10, and f(-3) is 20.
; CHECK-L: ( (fp.min |x| (|f| |x|)) (fp #b1 #b10000000 #b10000000000000000000000) )
; CHECK-L: ( (|f| (fp.abs |x|)) (fp #b0 #b10000010 #b01000000000000000000000) )
; min(3, 10) = 3, max(3, 10) = 10, 3 + 10 = 13.
; CHECK-L: ( (let ((|?let_k_0| (fp.abs |x|))) (fp.min |?let_k_0| (|f| |?let_k_0|))) (fp #b0 #b10000000 #b10000000000000000000000) )
; CHECK-L: ( (let ((|?let_k_0| (fp.abs |x|))) (fp.max |?let_k_0| (|f| |?let_k_0|))) (fp #b0 #b10000010 #b01000000000000000000000) )
; CHECK-L: ( (let ((|?let_k_0| (fp.abs |x|))) (fp.add RTN |?let_k_0| (|f| |?let_k_0|))) (fp #b0 #b10000010 #b10100000000000000000000) )
; A Bool-codomain application over the same computed actual, reached inside a
; float-valued term through the mux it selects: p(3) holds, so min(3, x) = -3.
; CHECK-L: ( (let ((|?let_k_0| (fp.abs |x|))) (fp.min |?let_k_0| (ite (|p| |?let_k_0|) |x| |y|))) (fp #b1 #b10000000 #b10000000000000000000000) )
; A bit-vector-codomain application over it, read back into the float layer:
; w(3) is 5, and min(3, 5) = 3.
; CHECK-L: ( (let ((|?let_k_0| (fp.abs |x|))) (fp.min |?let_k_0| ((_ to_fp 8 24) RNE (|w| |?let_k_0|)))) (fp #b0 #b10000000 #b10000000000000000000000) )
; CHECK: REACHED-END
;
(set-option :produce-models true)
(set-logic QF_UFBVFP)
(declare-fun f ((_ FloatingPoint 8 24)) (_ FloatingPoint 8 24))
(declare-fun p ((_ FloatingPoint 8 24)) Bool)
(declare-fun w ((_ FloatingPoint 8 24)) (_ BitVec 8))
(declare-const x (_ FloatingPoint 8 24))
(declare-const y (_ FloatingPoint 8 24))
(assert (= x ((_ to_fp 8 24) RNE (- 3.0))))
(assert (= y ((_ to_fp 8 24) RNE 1.0)))
(assert (= (f x) ((_ to_fp 8 24) RNE 20.0)))
(assert (= (f (fp.abs x)) ((_ to_fp 8 24) RNE 10.0)))
(assert (p (fp.abs x)))
(assert (= (w (fp.abs x)) #x05))
(check-sat)
(get-value ((fp.min x (f x))))
(get-value ((f (fp.abs x))))
(get-value ((fp.min (fp.abs x) (f (fp.abs x)))))
(get-value ((fp.max (fp.abs x) (f (fp.abs x)))))
(get-value ((fp.add RTN (fp.abs x) (f (fp.abs x)))))
(get-value ((fp.min (fp.abs x) (ite (p (fp.abs x)) x y))))
(get-value ((fp.min (fp.abs x) ((_ to_fp 8 24) RNE (w (fp.abs x))))))
(echo "REACHED-END")
