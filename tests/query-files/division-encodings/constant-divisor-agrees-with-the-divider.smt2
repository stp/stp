; A division or remainder by a constant is encoded through its defining
; relation, x = c*q + r with r < c, the product a shift-and-add of the fresh
; quotient over the constant's set bits. Each query below divides by the
; constant twice: once written as the constant, which takes the relation,
; and once as (c & d) | (c & e) under d | e = all ones, which is the constant
; in every model but not one the simplifier or the constant-bit propagation
; can see -- an equality pinning a symbol to c would be substituted, two
; bounds on it are resolved by the domain analysis, and (c & d) | (c & ~d)
; folds for c all ones -- so that side is the divider over a divisor the
; blast does not know. The two disagreeing is unsatisfiable
; exactly when the encodings agree on every dividend. At eight bits, with
; the width threshold lowered to reach the relation, that is every dividend
; and every constant of the shapes below: a power of two, an odd number,
; three, all ones but the lowest, and the top bit alone. All ones is not
; among them: (c & d) | (c & e) is then d | e, which the assertion pins.
;
; RUN: %solver --bb.div-by-const-width=8 %s | %OutputCheck %s
; RUN: %solver --bb.div-by-const-width=8 --bb.div-by-mult=1 %s | %OutputCheck %s
; RUN: %solver --bb.div-by-const-width=8 --incremental=on %s | %OutputCheck %s
; CHECK: ^unsat$
; CHECK: ^unsat$
; CHECK: ^unsat$
; CHECK: ^unsat$
; CHECK: ^unsat$
; CHECK: ^unsat$
; CHECK: ^unsat$
; CHECK: ^unsat$
; CHECK: ^unsat$
; CHECK: ^unsat$
;
; EXPECT: unsat, ten times
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const d (_ BitVec 8))
(declare-const e (_ BitVec 8))
(assert (= (bvor d e) #xff))
(push 1)
(assert (distinct (bvudiv x #x10) (bvudiv x (bvor (bvand #x10 d) (bvand #x10 e)))))
(check-sat)
(pop 1)
(push 1)
(assert (distinct (bvurem x #x10) (bvurem x (bvor (bvand #x10 d) (bvand #x10 e)))))
(check-sat)
(pop 1)
(push 1)
(assert (distinct (bvudiv x #x0b) (bvudiv x (bvor (bvand #x0b d) (bvand #x0b e)))))
(check-sat)
(pop 1)
(push 1)
(assert (distinct (bvurem x #x0b) (bvurem x (bvor (bvand #x0b d) (bvand #x0b e)))))
(check-sat)
(pop 1)
(push 1)
(assert (distinct (bvudiv x #x03) (bvudiv x (bvor (bvand #x03 d) (bvand #x03 e)))))
(check-sat)
(pop 1)
(push 1)
(assert (distinct (bvurem x #x03) (bvurem x (bvor (bvand #x03 d) (bvand #x03 e)))))
(check-sat)
(pop 1)
(push 1)
(assert (distinct (bvudiv x #xfe) (bvudiv x (bvor (bvand #xfe d) (bvand #xfe e)))))
(check-sat)
(pop 1)
(push 1)
(assert (distinct (bvurem x #xfe) (bvurem x (bvor (bvand #xfe d) (bvand #xfe e)))))
(check-sat)
(pop 1)
(push 1)
(assert (distinct (bvudiv x #x80) (bvudiv x (bvor (bvand #x80 d) (bvand #x80 e)))))
(check-sat)
(pop 1)
(push 1)
(assert (distinct (bvurem x #x80) (bvurem x (bvor (bvand #x80 d) (bvand #x80 e)))))
(check-sat)
(pop 1)
