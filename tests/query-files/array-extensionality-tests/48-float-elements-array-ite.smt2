; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; A float-element array if-then-else as the operand of an array
; equality.
;
; Written when the if-then-else was eliminated into a fresh replacement
; array, which had to be given the element format of the branches it
; stood for -- without it, the equalities minted over the replacement
; built their witness clauses against a format of (0, 0). Nothing is
; replaced now: the if-then-else stays a term and the checker reaches
; its branches with the T rules, under a guard on the candidate's p, so
; there is no replacement left to carry a format. Kept as coverage of
; the shape -- the element sort still has to reach the witness clauses
; the two disequalities are refuted through.
;
; Unsat by cases on p: d is a if p and b otherwise, and both are
; asserted to differ from d.
(set-logic QF_ABVFP)
(declare-fun p () Bool)
(declare-fun a () (Array (_ BitVec 2) (_ FloatingPoint 8 24)))
(declare-fun b () (Array (_ BitVec 2) (_ FloatingPoint 8 24)))
(declare-fun d () (Array (_ BitVec 2) (_ FloatingPoint 8 24)))
(assert (= (ite p a b) d))
(assert (not (= a d)))
(assert (not (= b d)))
(check-sat)
