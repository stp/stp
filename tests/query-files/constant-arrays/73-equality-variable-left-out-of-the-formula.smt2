; RUN: %solver --array-equality %s | %OutputCheck %s
; RUN: %solver --array-equality --incremental=on %s | %OutputCheck %s
; RUN: %solver --array-equality -d %s | %OutputCheck %s
; As 70, the if-then-else becomes its constant-array branch only in
; preprocessing, and its witness read folds to #x7; the other side's reads
; #xf. The witness clause, "the equality holds or the witness reads differ",
; then holds without the equality's abstraction variable, and p, which occurs
; only positively, is set true, taking the query's own disjunction with it.
; The variable is left in no constraint at all. The batch driver gave SAT
; variables only to what the bit-blast reached and to read abstractions, so
; the candidate had no value for it, and the consistency checker, which reads
; it, stopped with an internal error; the incremental driver allocated one.
; The variable is unconstrained, and the equality false in every model.
; Likewise for distinct, and for Boolean cells.
(set-logic QF_ABV)
(declare-fun p () Bool)
(declare-fun y () (_ BitVec 4))
(declare-fun a () (Array (_ BitVec 2) (_ BitVec 4)))
(declare-fun b () (Array (_ BitVec 2) Bool))
(assert (= (bvand y #x1) #x1))
(push 1)
(assert (or (= (ite (= ((_ extract 0 0) y) #b1)
                    ((as const (Array (_ BitVec 2) (_ BitVec 4))) #x7)
                    a)
               ((as const (Array (_ BitVec 2) (_ BitVec 4))) #xf))
            p))
; CHECK: ^sat$
(check-sat)
(assert (not p))
; CHECK: ^unsat$
(check-sat)
(pop 1)
(push 1)
(assert (or (distinct (ite (= ((_ extract 0 0) y) #b1)
                          ((as const (Array (_ BitVec 2) (_ BitVec 4))) #x7)
                          a)
                      ((as const (Array (_ BitVec 2) (_ BitVec 4))) #xf))
            p))
; CHECK: ^sat$
(check-sat)
(pop 1)
(push 1)
(assert (or (= (ite (= ((_ extract 0 0) y) #b1)
                    ((as const (Array (_ BitVec 2) Bool)) true)
                    b)
               ((as const (Array (_ BitVec 2) Bool)) false))
            p))
; CHECK: ^sat$
(check-sat)
(assert (not p))
; CHECK: ^unsat$
(check-sat)
(pop 1)
