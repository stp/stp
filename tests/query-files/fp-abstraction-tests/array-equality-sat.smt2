; A satisfiable query with an active array equality and an abstracted
; product whose first candidate the exact product refutes. The refutation
; leaves a floating-point lemma pending and nothing for the array checker,
; and the batch refinement loop must take that as the round's progress
; rather than abort for a round with neither a decision nor an array
; lemma. Once aborted here.
;
; RUN: %solver --array-equality %s | %OutputCheck %s
; RUN: %solver --array-equality --fp-abstraction=true -d %s | %OutputCheck %s
; CHECK: ^sat$
(set-logic QF_ABVFP)
(declare-fun a () (Array (_ BitVec 4) (_ FloatingPoint 8 24)))
(declare-fun b () (Array (_ BitVec 4) (_ FloatingPoint 8 24)))
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(declare-fun i () (_ BitVec 4))
(assert (= a b))
(assert (= (select a i) (fp.mul RNE x y)))
(assert (fp.gt x ((_ to_fp 8 24) RNE 1.5)))
(assert (fp.lt x ((_ to_fp 8 24) RNE 4.0)))
(assert (fp.gt y ((_ to_fp 8 24) RNE 1.5)))
(assert (fp.eq (select b i) ((_ to_fp 8 24) RNE 6.0)))
(check-sat)
