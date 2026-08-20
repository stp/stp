; --aig-core-simplification builds its own AIG, ahead of the bit-blaster and
; out of its manager, so the budget has to be handed to it separately. The
; pass is an optimisation: an exhausted budget makes it keep the formula it
; was given rather than abandon the query, and only the blast that follows
; decides the verdict.
;
; Ten interleaved bvult atoms under an xor tree and three ites survive the
; word-level simplifier as a propositional core of ~74 AND gates -- enough
; for a budget of 40 to stop the pass. The blast that follows needs far more
; than 40 for ten 8-bit comparisons, so it is stopped too and the query is
; abandoned; no budget can separate the two, since the pass is always the
; cheaper of them.
;
; RUN: %solver --SMTLIB2 -s --aig-core-simplification=1 --aig-node-budget 40 %s 2>&1 >/dev/null | %OutputCheck --check-prefix=ABANDONED %s
; RUN: %solver --SMTLIB2 --aig-core-simplification=1 %s | %OutputCheck --check-prefix=ANSWER %s
; RUN: %solver --SMTLIB2 %s | %OutputCheck --check-prefix=ANSWER %s
;
; ABANDONED: AIG core simplification abandoned at [0-9]+ nodes
; ANSWER: ^sat$
(set-logic QF_BV)
(declare-const x0 (_ BitVec 8))
(declare-const x1 (_ BitVec 8))
(declare-const x2 (_ BitVec 8))
(declare-const x3 (_ BitVec 8))
(declare-const x4 (_ BitVec 8))
(declare-const x5 (_ BitVec 8))
(declare-const x6 (_ BitVec 8))
(declare-const x7 (_ BitVec 8))
(declare-const x8 (_ BitVec 8))
(declare-const x9 (_ BitVec 8))
(assert
 (let ((a0 (bvult x0 x1)) (a1 (bvult x1 x2)) (a2 (bvult x2 x3)) (a3 (bvult x3 x4))
       (a4 (bvult x4 x5)) (a5 (bvult x5 x6)) (a6 (bvult x6 x7)) (a7 (bvult x7 x8))
       (a8 (bvult x8 x9)) (a9 (bvult x9 x0)))
 (let ((t (xor a0 a1 a2 a3 a4 a5 a6 a7 a8 a9)))
 (let ((u (ite t (xor t a0) (and t a1))))
 (let ((v (ite u (xor u a1) (and u a2))))
      (ite v (xor v a2) (and v a3)))))))
(check-sat)
