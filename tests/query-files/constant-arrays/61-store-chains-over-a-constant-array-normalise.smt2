; RUN: %solver %s | %OutputCheck %s
; A store chain over a constant array is kept in one form as it is built: a
; store of the default goes, a store shadowed by a later one at the same
; constant index goes, and the rest are ordered by index, the smallest
; innermost. The model prints that form, and two spellings of one array
; are one term.
(set-option :produce-models true)
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 4) (_ BitVec 4)))
(declare-fun b () (Array (_ BitVec 1) (_ BitVec 8)))
(declare-fun i () (_ BitVec 4))
(declare-fun z () (_ BitVec 4))
(push 1)
(assert (= a (store (store (store (store ((as const (Array (_ BitVec 4) (_ BitVec 4))) #x0) #x3 #x5) #x2 #x0) #x1 #x6) #x3 #x7)))
; CHECK: ^sat$
(check-sat)
; CHECK-NEXT: ^\($
; CHECK-NEXT: \|a\| \(store \(store \(\(as const \(Array \(_ BitVec 4\) \(_ BitVec 4\)\)\) #x0\) #x1 #x6\) #x3 #x7\)
(get-value (a))
(pop 1)
; Every cell of a one-bit-indexed array written: the constant array.
(push 1)
(assert (= b (store (store ((as const (Array (_ BitVec 1) (_ BitVec 8))) #x00) #b1 #x07) #b0 #x07)))
; CHECK: ^sat$
(check-sat)
; CHECK-NEXT: ^\($
; CHECK-NEXT: \|b\| \(\(as const \(Array \(_ BitVec 1\) \(_ BitVec 8\)\)\) #x07\)
(get-value (b))
(pop 1)
; Permuted, with a shadowed store and a store of the default: one term.
(push 1)
(assert (not (= (store (store (store ((as const (Array (_ BitVec 4) (_ BitVec 4))) #x0) #x1 #x6) #x3 #x7) #x9 #x0)
                (store (store (store ((as const (Array (_ BitVec 4) (_ BitVec 4))) #x0) #x3 #x1) #x1 #x6) #x3 #x7))))
; CHECK: ^unsat$
(check-sat)
(pop 1)
; The default written onto the constant array at a symbolic index, with a
; symbolic default.
(push 1)
(assert (not (= (store ((as const (Array (_ BitVec 4) (_ BitVec 4))) z) i z)
                ((as const (Array (_ BitVec 4) (_ BitVec 4))) z))))
; CHECK: ^unsat$
(check-sat)
(pop 1)
; A store of the default above a store at a symbolic index stays: the
; symbolic index may be the same one.
(push 1)
(assert (= i #x2))
(assert (= (select (store (store ((as const (Array (_ BitVec 4) (_ BitVec 4))) #x0) i #x5) #x2 #x0) #x2) #x5))
; CHECK: ^unsat$
(check-sat)
(pop 1)
