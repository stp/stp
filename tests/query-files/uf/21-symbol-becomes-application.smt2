; A symbol equated with an application becomes that application, so a and b
; below are both (f (bvadd x #x01)) once x = y has been read as well, and the
; two quotients are the same term. Without the pass they are two result
; symbols, and refuting the query means proving two 8-bit dividers agree
; whenever their inputs do.
;
; RUN: %solver -s --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver -s --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: UF: pre-lowering substituted 3 symbol\(s\) and 0 application\(s\)
; CHECK-NOT: installed congruence lemma
; CHECK: ^unsat$
;
; EXPECT: unsat
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
(assert (= (f (bvadd x #x01)) a))
(assert (= (f (bvadd y #x01)) b))
(assert (= x y))
(assert (distinct (bvudiv a #x07) (bvudiv b #x07)))
(check-sat)
