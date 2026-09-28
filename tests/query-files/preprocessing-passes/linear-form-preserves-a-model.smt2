; The rewrite is an identity: it collects the terms of a combination and
; picks one spelling for the result, which changes neither the value the
; combination takes nor which assignments give it that value. A query with
; a model keeps it, and the pass answering something else on one of these
; would mean the arithmetic had been changed rather than the spelling.
; RUN: %solver -s --linear-form=1 %s 2>&1 | %OutputCheck %s
; CHECK: Terms given a canonical form:[1-9]
; CHECK: ^sat$
;
; RUN: %solver %s | %OutputCheck --check-prefix=OFF %s
; OFF: ^sat$
(set-logic QF_BV)
(declare-fun a () (_ BitVec 16))
(declare-fun b () (_ BitVec 16))
(declare-fun c () (_ BitVec 16))
(assert (= (bvadd (bvmul (_ bv3 16) (bvadd a b)) c) (_ bv100 16)))
(assert (= (bvsub (bvshl a (_ bv1 16)) (bvadd b b)) (_ bv8 16)))
(assert (bvult (bvadd a (bvmul (_ bv65535 16) b)) (_ bv50 16)))
(assert (distinct a b c))
(check-sat)
(exit)
