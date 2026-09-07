; A UF solve whose query holds a wide multiplication abstracts it as
; --bv-term-abstraction would, without being asked: the 128-bit product
; below is a free vector of bits until a candidate contradicts it, and this
; query never needs it exactly -- z names the product, so the two
; applications are congruent by the eager constraint alone.
;
; RUN: %solver -s --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; CHECK: UF: abstracting wide arithmetic for this solve
; CHECK: ^unsat$
;
; The policy is a policy, not a fact about the query: it can be refused.
; RUN: %solver -s --uninterpreted-functions --uf-bv-term-abstraction=off --incremental=off %s 2>&1 | %OutputCheck --check-prefix=OFF %s
; OFF-NOT: abstracting wide arithmetic
; OFF: ^unsat$
;
; And it leaves the general flag as it found it for the next solve, which
; the second query below checks: without an application of its own it is
; a plain bit-vector query, and a plain bit-vector query is encoded exactly.
; RUN: %solver -s --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck --check-prefix=NEXT %s
; NEXT: abstracting wide arithmetic for this solve
; NEXT: ^unsat$
; NEXT-NOT: BV term abstraction on
; NEXT: ^sat$
;
; EXPECT: unsat, then sat
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 128)) (_ BitVec 8))
(declare-const x (_ BitVec 128))
(declare-const y (_ BitVec 128))
(declare-const z (_ BitVec 128))
(push 1)
(assert (= z (bvmul x y)))
(assert (= (f (bvmul x y)) #x01))
(assert (= (f z) #x02))
(check-sat)
(pop 1)
(assert (= (bvmul x y) #x00000000000000000000000000000006))
(check-sat)
