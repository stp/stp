; Two spellings of one sum, each feeding its own signed division.
;
;   -2*Z + p1 - (p2 + p2)      and      p1 - (p2 + p2 + 2*Z)
;
; are the same combination written two ways, so the divisions are the same
; division. Left as two terms they are two dividers, and the answer has to
; come out of the SAT solver reasoning through both; given one canonical
; spelling they are one node and the query collapses.
; RUN: %solver -s --linear-form=1 %s 2>&1 | %OutputCheck %s
; CHECK: Terms given a canonical form:[1-9]
; CHECK: ^unsat$
;
; The same query with the pass off. It is the same theorem either way --
; this is an identity, not an approximation -- so a disagreement between the
; two legs is the pass changing an answer rather than the speed it reaches
; it at.
; RUN: %solver %s | %OutputCheck --check-prefix=OFF %s
; OFF: ^unsat$
(set-logic QF_BV)
(declare-fun p0 () (_ BitVec 32))
(declare-fun p1 () (_ BitVec 32))
(declare-fun p2 () (_ BitVec 32))
(assert
  (let ((z (bvsdiv p0 (_ bv2 32))))
    (not (=
      (bvsdiv (bvadd (bvmul (_ bv4294967294 32) z)
                     (bvadd p1 (bvmul (_ bv4294967295 32) (bvadd p2 p2))))
              (_ bv2 32))
      (bvsdiv (bvadd p1
                     (bvmul (_ bv4294967295 32)
                            (bvadd p2 (bvadd p2 (bvmul (_ bv2 32) z)))))
              (_ bv2 32))))))
(check-sat)
(exit)
