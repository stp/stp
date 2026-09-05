; An identical re-pushed extensionality stack must reuse its encoded block
; even when the scoped preprocessing pass eliminates an unconstrained
; variable.
;
; The block cache is keyed on the transformed node, and the scoped pass runs
; in front of it. RemoveUnconstrained names its stand-in variables from a
; counter, so once a stand-in survives into the output -- which needs the
; replaced parent term to have two or more uses, as (bvadd u x) does here --
; the same stack lowered to a DIFFERENT node on every round, missed the
; cache, and re-encoded the whole formula. That is unbounded growth on the
; repeat-a-query workload the block cache exists for: measured at twenty
; extra SAT variables per identical round before the pass was memoised by
; input node, against a flat count after.
;
; array-eq-block-reuse.smt2 covers the same reuse without an eliminable
; unconstrained variable, so it never exercised the non-deterministic stage.
; The answers are covered elsewhere; stdout and stderr interleave unreliably
; under a pipe, so this pins only the reuse decision, which is on stderr.
; RUN: %solver --array-equality --incremental -s %s 2>&1 | %OutputCheck %s
; RUN: %solver --array-equality --incremental-auto-engage-at 1 -s %s 2>&1 | %OutputCheck %s
(set-logic QF_ABV)
(declare-fun A () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun B () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun u () (_ BitVec 8))
(declare-fun x () (_ BitVec 8))
(assert (= A B))
(push 1)
(assert (bvult (bvadd u x) #x10))
(assert (bvugt (bvadd u x) #x02))
; CHECK: block of 2 levels encoded
(check-sat)
(pop 1)
(push 1)
(assert (bvult (bvadd u x) #x10))
(assert (bvugt (bvadd u x) #x02))
; the identical stack must hit the block cache, not mint a fresh encoding
; CHECK: block of 2 levels reused
(check-sat)
(pop 1)
(push 1)
(assert (bvult (bvadd u x) #x10))
(assert (bvugt (bvadd u x) #x02))
; CHECK: block of 2 levels reused
(check-sat)
(exit)
