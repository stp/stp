; A floating-point result used as a floating-point operand, and a
; rounding-mode result used *as* the rounding mode. This is what admitting
; the sorts is for, and until it is pinned here nothing tests it directly.
;
; Both need the application node to answer its own format. It is not carried
; by any operand -- the declaration identity names it -- so ASTNode's format
; derivation has a UF_APPLY arm reading the codomain's source sort. Without
; it the application is an FP-sorted node of no format, which types as a
; plain bit-vector: fp.add refuses it as having a different format from its
; other operand, and fp.abs builds a (0, 0)-format result that blasts to the
; wrong bits.
;
; The last two rows are the same two sorts read back from inside a term for
; an application the solve never reached, which resolves through the
; certified seed rather than at the root.
;
; RUN: %solver --uninterpreted-functions --check-sanity --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --check-sanity --incremental=on %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --uf-ackermann=on --incremental=off %s 2>&1 | %OutputCheck %s
;
; The term half of each pair is printed through get-value's letizing entry
; point, so a subterm named twice comes back as a let binding rather than
; twice over -- (q i) below is one such subterm.
;
; CHECK: ^sat
; CHECK-L: ( (|q| |i|) (fp #b0 #b10000000 #b00000000000000000000000) )
; 1.0 + 1.0 = 2.0, under a literal rounding mode ...
; CHECK-L: ( (let ((|?let_k_0| (|q| |i|))) (fp.add RNE |?let_k_0| |?let_k_0|)) (fp #b0 #b10000001 #b00000000000000000000000) )
; CHECK-L: ( (fp.isNaN (|q| |i|)) false )
; CHECK-L: ( (|k| |i|) RTZ )
; ... and under one an uninterpreted function computed.
; CHECK-L: ( (let ((|?let_k_0| (|q| |i|))) (fp.add (|k| |i|) |?let_k_0| |?let_k_0|)) (fp #b0 #b10000001 #b00000000000000000000000) )
; CHECK-L: ( (fp.isNaN (|q|  #xE)) false )
; CHECK-L: ( (= RNE (|k|  #xE)) true )
; CHECK: REACHED-END
;
(set-logic QF_UFBVFP)
(set-option :produce-models true)
(declare-fun q ((_ BitVec 4)) (_ FloatingPoint 8 24))
(declare-fun k ((_ BitVec 4)) RoundingMode)
(declare-const i (_ BitVec 4))
(assert (= i #x1))
(assert (= (q i) (fp #b0 #b10000000 #b00000000000000000000000)))
(assert (= (k i) RTZ))
(check-sat)
(get-value ((q i)))
(get-value ((fp.add RNE (q i) (q i))))
(get-value ((fp.isNaN (q i))))
(get-value ((k i)))
(get-value ((fp.add (k i) (q i) (q i))))
(get-value ((fp.isNaN (q #xe))))
(get-value ((= (k #xe) RNE)))
(echo "REACHED-END")
