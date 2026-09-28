; RUN: %solver --SMTLIB2 %s | %OutputCheck %s
;
; Reading values back out of the committed exact model, over both kinds of
; entry it holds.
;
; The model stores one entry per Real symbol, and defineApplicationValues
; appends one more for each uninterpreted application the solve lowered, so
; that a term over the application can be valued by the name the arithmetic
; actually used. findSymbol answers from that store, and it used to answer by
; scanning it: once per symbol leaf of every term the verifier evaluates,
; against every entry in the model. It is now indexed by node number, which
; hash-consing puts in bijection with the node.
;
; What that index must not do is lose an entry or shadow one. Both insertion
; points are exercised here -- five plain symbols, and two applications that
; congruence forces to agree without being the same node -- and every value
; is read back. p and q are equal, so f(p) and f(q) are one congruence class
; and must report the same value; s and t are only reachable through the
; arithmetic, so they come from the solve rather than from a bound.
; Fix r relative to f(q), so the expected values do not depend on which
; valid witness a backend chooses for the strict inequality.
(set-logic QF_UFLRA)
(set-option :produce-models true)
(declare-fun f (Real) Real)
(declare-fun p () Real)
(declare-fun q () Real)
(declare-fun r () Real)
(declare-fun s () Real)
(declare-fun t () Real)
(assert (= p 3.0))
(assert (= q p))
(assert (= (f p) 7.0))
(assert (> r (f q)))
(assert (= r (+ (f q) 1.0)))
(assert (= s (- r 100.0)))
(assert (= t (+ s p q)))
; CHECK: ^sat$
(check-sat)
; CHECK-L: (|p| 3)
; CHECK-NEXT-L: (|q| 3)
; CHECK-NEXT-L: (|r| 8)
; CHECK-NEXT-L: (|s| (- 92))
; CHECK-NEXT-L: (|t| (- 86))
; CHECK-NEXT-L: ((|f| |p|) 7)
; CHECK-NEXT-L: ((|f| |q|) 7)
(get-value (p q r s t (f p) (f q)))
(exit)
