; The same promotion defect as unit-promotion-repreparation.smt2, reached
; through a definition PropagateEqualities only finds after chaining an
; earlier substitution.
;
; recogniseDefinition sees (= u #x03) and puts u := 3 in the context, but it
; cannot read (= (bvadd p u) #x07) as a definition of p. Only after the
; context rewrite does the simplifying factory expose p := 4 to the
; propagator, so the elimination exists while the context does not carry p --
; a different route into the same promoted-level skip, and one no context
; re-join can cover.
;
; Constant-bit propagation independently re-derives p = 4 here, so this file
; is pinned with the pass disabled: it is a regression for promotion, not for
; whichever other mechanism happens to be masking it.
; RUN: %solver --incremental --disable-cbitp %s | %OutputCheck %s
; RUN: %solver --incremental-auto-engage-at 1 --disable-cbitp %s | %OutputCheck %s
; RUN: %solver --incremental --disable-cbitp --check-sanity %s | %OutputCheck %s
(set-logic QF_BVFP)
(declare-fun f () Float32)
(declare-fun u () (_ BitVec 8))
(declare-fun p () (_ BitVec 8))
(declare-fun z () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(assert (bvult y #xff))
(assert (fp.gt f (_ +zero 8 24)))
(push 1)
(assert (= u #x03))
(assert (= (bvadd p u) #x07))
(assert (bvugt z #x05))
(push 1)
(assert (bvugt y #x00))
(check-sat)
(pop 1)
(push 1)
(assert (bvugt y #x01))
(check-sat)
(pop 1)
(push 1)
(assert (bvugt y #x02))
(check-sat)
(pop 1)
(push 1)
(assert (bvugt y #x03))
(check-sat)
(pop 1)
(push 1)
(assert (bvugt y #x04))
(check-sat)
(pop 1)
(push 1)
(assert (bvugt y #x05))
(check-sat)
(pop 1)
(push 1)
(assert (bvugt y #x06))
(check-sat)
(pop 1)
(push 1)
(assert (bvugt y #x07))
(check-sat)
(pop 1)
(push 1)
(assert (bvugt y #x08))
(check-sat)
(pop 1)
(push 1)
(assert (bvugt y #x09))
(check-sat)
(pop 1)
(push 1)
(assert (bvugt y #x0a))
(check-sat)
(pop 1)
(push 1)
(assert (bvugt y #x0b))
(check-sat)
(pop 1)
(push 1)
(assert (bvugt y #x01))
(push 1)
(assert (= p #xff))
; p is pinned to 4 by the promoted level; the churn rounds are all sat
; CHECK: ^unsat
(check-sat)
(exit)
