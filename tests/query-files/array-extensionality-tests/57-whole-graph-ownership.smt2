; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; CHECK-NEXT: ^unsat
; CHECK-NEXT: ^unsat
; CHECK-NEXT: ^unsat
; Once any array equality activates extensional reasoning, one checker owns
; every reachable array read. These four scopes exercise arrays disconnected
; from the activating equality: congruence, read-over-write, array ITE, and a
; read-equals-constant equation that preprocessing must not discard.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 4) (_ BitVec 4)))
(declare-fun b () (Array (_ BitVec 4) (_ BitVec 4)))
(declare-fun x () (Array (_ BitVec 4) (_ BitVec 4)))
(declare-fun y () (Array (_ BitVec 4) (_ BitVec 4)))
(declare-fun i () (_ BitVec 4))
(declare-fun j () (_ BitVec 4))
(declare-fun p () Bool)

; Congruence on an array disconnected from a = b.
(push 1)
(assert (= a b))
(assert (not (bvult i j)))
(assert (not (bvult j i)))
(assert (distinct (select x i) (select x j)))
(check-sat)
(pop 1)

; The same disconnected component contains a write node.
(push 1)
(assert (= a b))
(assert (not (bvult i j)))
(assert (not (bvult j i)))
(assert (distinct (select (store x i #x7) j) #x7))
(check-sat)
(pop 1)

; Whichever branch is live, the read of this disconnected array ITE must
; agree with one of the branch reads.
(push 1)
(assert (= a b))
(assert (distinct (select (ite p x y) i) (select x i)))
(assert (distinct (select (ite p x y) i) (select y i)))
(check-sat)
(pop 1)

; Both reads must survive preprocessing and meet in rule C at i = j.
(push 1)
(assert (= a b))
(assert (= (select x i) #x5))
(assert (not (bvult i j)))
(assert (not (bvult j i)))
(assert (distinct (select x j) #x5))
(check-sat)
(pop 1)
