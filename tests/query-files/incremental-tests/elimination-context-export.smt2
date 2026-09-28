; Definition privacy is decided over what reaches the ENCODER, not over the
; raw assertion stack.
;
; recogniseDefinition needs a symbol on one side, so it reads the conjunct
; below as y := ~v and puts a context body naming v in front of every deeper
; level. PropagateEqualities reads the same conjunct through its BVNOT rule
; as v := ~y and offers v for elimination -- and v looks private, because no
; other RAW level names it. Eliminating it drops the equation while the
; deeper level, encoded through the context over (bvnot v), keeps the
; occurrence: level one is then constrained in terms of y, level two in terms
; of v, and nothing relates them.
;
; The re-join that normally repairs this by feeding the eliminated definition
; back into the context cannot help here: expanding ~y under y := ~v yields
; v, so the occurs-check declines it -- silently, with the elimination left
; standing. levelPrivate must therefore refuse v itself.
;
; y = ~v and y*y = y force y into {0,1}, so the deeper y > 1 is unsat. The
; multiplications keep constant-bit propagation from refuting the query on
; its own, which would mask the defect.
; RUN: %solver --incremental %s | %OutputCheck %s
; RUN: %solver --incremental-auto-engage-at 1 %s | %OutputCheck %s
; RUN: %solver --incremental --check-sanity %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun v () (_ BitVec 8))
(declare-fun p () (_ BitVec 8))
(push 1)
; keeps (bvnot v) alive and numbered before y is declared
(assert (bvult (bvnot v) p))
(declare-fun y () (_ BitVec 8))
(assert (= (bvnot v) y))
(assert (= (bvmul y y) y))
(declare-fun w1 () (_ BitVec 8))
(declare-fun w2 () (_ BitVec 8))
(declare-fun w3 () (_ BitVec 8))
(declare-fun w4 () (_ BitVec 8))
(declare-fun w5 () (_ BitVec 8))
(declare-fun w6 () (_ BitVec 8))
(declare-fun w7 () (_ BitVec 8))
(declare-fun w8 () (_ BitVec 8))
(declare-fun w9 () (_ BitVec 8))
(declare-fun w10 () (_ BitVec 8))
(assert (= w1 (bvmul v w2)))
(assert (= w3 (bvmul v w4)))
(assert (= w5 (bvmul v w6)))
(assert (= w7 (bvmul v w8)))
(assert (= w9 (bvmul v w10)))
(push 1)
(assert (bvugt y #x01))
; a stale elimination answers sat here
; CHECK: ^unsat
(check-sat)
(exit)
