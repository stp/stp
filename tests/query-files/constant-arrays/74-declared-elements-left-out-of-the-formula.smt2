; RUN: %solver --array-equality %s | %OutputCheck %s
; RUN: %solver --array-equality --incremental=on %s | %OutputCheck %s
; RUN: %solver --array-equality -d %s | %OutputCheck %s
; As 73, over a declared index sort, whose elements the checker reads to
; bound the sort's domain (65): the symbols of the sort, and the witness
; index of each equality over it. Once both witness reads have folded to
; defaults, the witness index occurs nowhere, and the batch driver had no
; value for it even with the equality asserted; and a symbol of the sort goes
; with the last constraint on it, here a disjunction p satisfies. Each is
; unconstrained, and gets a value like the equality's own variable.
(set-logic QF_AUFBV)
(declare-sort U 0)
(declare-fun p () Bool)
(declare-fun y () (_ BitVec 4))
(declare-fun a () (Array U (_ BitVec 4)))
(assert (= (bvand y #x1) #x1))
(push 1)
(assert (distinct (ite (= ((_ extract 0 0) y) #b1)
                       ((as const (Array U (_ BitVec 4))) #x7)
                       a)
                  ((as const (Array U (_ BitVec 4))) #xf)))
; CHECK: ^sat$
(check-sat)
(pop 1)
(push 1)
(assert (or (= (ite (= ((_ extract 0 0) y) #b1)
                    ((as const (Array U (_ BitVec 4))) #x7)
                    a)
               ((as const (Array U (_ BitVec 4))) #xf))
            p))
; CHECK: ^sat$
(check-sat)
(assert (not p))
; CHECK: ^unsat$
(check-sat)
(pop 1)
(push 1)
(declare-fun u () U)
(declare-fun v () U)
(assert (or p (distinct u v)))
(assert (not (= a ((as const (Array U (_ BitVec 4))) #x7))))
; CHECK: ^sat$
(check-sat)
(pop 1)
