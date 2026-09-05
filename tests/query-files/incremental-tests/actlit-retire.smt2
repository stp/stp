; A multi-conjunct level is assumed through one activation literal whose
; implications persist after the pop. Once its root set has not been
; assumed for many solves, the literal is retired: pinned false by a
; permanent unit, which satisfies the implications outright and fixes
; the variable so the solver never decides it again -- sound for
; activation variables and no others, because their ONLY clauses are
; the implications the pin satisfies. A retired root set that recurs
; mints a fresh activation literal, and the level must still bind.
; RUN: %solver -s --incremental %s 2>&1 | %OutputCheck %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
; two conjuncts: the level is assumed through an activation literal
(push 1)
(assert (bvult x #x10))
(assert (bvult y #x10))
; CHECK: ^sat
(check-sat)
(pop 1)
; seventeen unrelated solves age the entry out
(push 1)
(assert (distinct x #x20))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (distinct x #x21))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (distinct x #x22))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (distinct x #x23))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (distinct x #x24))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (distinct x #x25))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (distinct x #x26))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (distinct x #x27))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (distinct x #x28))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (distinct x #x29))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (distinct x #x2a))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (distinct x #x2b))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (distinct x #x2c))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (distinct x #x2d))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (distinct x #x2e))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (distinct x #x2f))
; CHECK: ^sat
(check-sat)
(pop 1)
; the age limit passes at this solve: the activation literal is pinned
(push 1)
(assert (distinct x #x30))
; CHECK: pinned 1 retired activation literals
; CHECK: ^sat
(check-sat)
(pop 1)
; the retired root set recurs: a fresh activation literal carries it,
; and its implications bind for real
(push 1)
(assert (bvult x #x10))
(assert (bvult y #x10))
; CHECK: ^sat
(check-sat)
(push 1)
(assert (bvuge x #x10))
; CHECK: ^unsat
(check-sat)
(pop 1)
(pop 1)
(exit)
