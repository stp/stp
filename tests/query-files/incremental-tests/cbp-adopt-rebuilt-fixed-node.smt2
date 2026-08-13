; A conjunct arriving at CBP adoption is a ctx-substituted form: the
; definer (= _x2 _x3) was folded out of the inner AND and re-joined on
; top, so the node no longer contains the raw inner AND the feed fixed
; TRUE.  Substituting the third conjunct's fixing (its bvsgt shell to
; FALSE) then REBUILDS exactly that inner AND -- hash-consing hands the
; substitution a node the walked DAG never contained, replace() maps
; the rebuilt node too, and the pinning-fact walk asserted nothing for
; it: the definer and the sdiv conjunct silently left the encoding.
; The model falsified the raw stack (_x4=0b00 falsifies the sdiv
; conjunct, which only 0b10/0b11 satisfy), and a second level
; contradicting the dropped conjunct turned the verdict itself wrong:
; sat on an unsat stack.  Found by murxla.  The adoption substitution
; is now restricted to entries occurring in the conjunct's own DAG --
; exactly the set the fact walk pins.
; RUN: %solver --incremental --check-sanity -s %s 2>&1 | %OutputCheck %s
; RUN: %solver --incremental --check-sanity %s | %OutputCheck --check-prefix=VERDICT %s
; RUN: %solver --incremental --incremental-cbp-reset --check-sanity %s | %OutputCheck --check-prefix=VERDICT %s
; RUN: %solver --incremental-auto-engage-at 1 --check-sanity %s | %OutputCheck --check-prefix=VERDICT %s
(push 1)
(declare-const _x0 (_ BitVec 2))
(declare-const _x2 (_ BitVec 1))
(declare-const _x3 (_ BitVec 1))
(declare-const _x4 (_ BitVec 2))
(assert (and (and (= _x2 _x3) (bvsgt (bvsdiv _x4 _x4) _x4)) (bvsle (bvlshr _x0 _x0) _x0)))
; The adoption must still fire -- the fix restricts what it may
; substitute, it does not retire the pass -- and --check-sanity
; validates the model against the raw stack.
; CHECK: cbp adopted
; CHECK: ^sat
; VERDICT: ^sat
(check-sat)
(push 1)
; Bit-level transfer functions learn nothing from a disequality, so no
; engine conflict masks the loss: only the encoded sdiv conjunct
; (forcing _x4 to 0b10 or 0b11) can refute these.  With it dropped,
; this answered sat.
(assert (and (distinct _x4 #b10) (distinct _x4 #b11)))
; CHECK: ^unsat
; VERDICT: ^unsat
(check-sat)
(pop 1)
; The disequalities retract; the replayed adoption must still carry
; the sdiv conjunct's strength, with a model that satisfies it.
; CHECK: ^sat
; VERDICT: ^sat
(check-sat)
(pop 1)
(exit)
