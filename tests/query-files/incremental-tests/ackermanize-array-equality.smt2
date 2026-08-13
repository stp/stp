; The driver's array-equality route used to switch --ackermanize off for
; the whole round with a blanket warning, where the batch pipeline first
; instantiates the equalities pointwise over the solve's access indexes
; (array-extensionality-tests/70..74) and stays on the eager path. Pin
; the batch behavior on the driver: no warning, no lazy-checker round,
; and read congruence still propagates across the equality -- across
; push/pop, with the repeat round reusing the encoded block.
; RUN: %solver -s --incremental --array-equality --ackermanize --check-sanity %s 2>&1 | %OutputCheck %s
; CHECK-NOT-L: Warning:
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun b () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun i () (_ BitVec 2))
(declare-fun j () (_ BitVec 2))
(assert (= a b))
(push 1)
; equal arrays read at possibly different indexes may differ
(assert (distinct (select a i) (select b j)))
; CHECK: ^sat
(check-sat)
(push 1)
; forcing the indexes equal contradicts the disequality through the
; instantiated equality: no lazy lemma round may be needed for this
(assert (= i j))
; CHECK: ^unsat
(check-sat)
(pop 1)
; CHECK: ^sat
(check-sat)
(pop 1)
; the repeat of the first stack shape reuses its block
; CHECK: ^sat
(check-sat)
