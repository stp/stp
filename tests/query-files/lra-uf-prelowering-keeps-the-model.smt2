; RUN: %solver --SMTLIB2 --check-sanity %s 2>&1 | %OutputCheck %s
;
; The satisfiable side: a wrong substitution can reach the right verdict and
; still publish a model that does not satisfy the query, which no unsat file
; here would notice. Every fact the rewrite uses is kept as the definition of
; the symbol it was used on, so the values below are the ones the query gave
; them, and `(f x)` is read back through the certified function model rather
; than through a symbol the rewrite removed.
;
; --check-sanity replays the parsed assertions against the published model
; and fails loudly if any evaluates to false, so it covers the arithmetic the
; CHECK-L lines do not name.
;
; This is uf/23-pre-lowering-keeps-the-model.smt2 with the sort changed; the
; Real model prints its values as rationals rather than as hex.
; CHECK: ^sat$
; CHECK-L: (|x| 5)
; CHECK-L: (|y| 5)
; CHECK-L: ((|f| |x|) 42)
; CHECK-L: ((|f| |y|) 42)
; CHECK-L: (|a| 42)
; CHECK-L: (|b| 43)
(set-logic QF_UFLRA)
(set-option :produce-models true)
(declare-fun f (Real) Real)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun a () Real)
(declare-fun b () Real)
(assert (= x 5.0))
(assert (= y x))
(assert (= a (f x)))
(assert (= (f y) 42.0))
(assert (= b (+ a 1.0)))
(check-sat)
(get-value (x))
(get-value (y))
(get-value ((f x)))
(get-value ((f y)))
(get-value (a))
(get-value (b))
