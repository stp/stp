; An extensionality-ROUTED round with no LIVE array equality: the raw
; conjunct carries an ARRAY_EQ (so the fragment routes every check-sat
; through the extensionality block), but the base-level unit p absorbs
; the disjunct before the block is assembled, so the round runs with the
; checker inactive and falls back to ordinary read refinement -- the
; hybrid the routing comment promises. That fallback refines over the
; ROUND registry's read symbols, and nothing totalised them: the
; extActive-gated totalisation covers only the checker's symbols, and
; the plain path's registry totalisation never runs here. The congruence
; axioms were then encoded over missing-bit markers -- a crash under
; CaDiCaL's factor translation, silently corrupted axioms on every
; other backend.
;
; The reads use one bit of a 32-bit value, so the abstraction variables
; are only partially inside the block's cone; the indices are equated
; through a bvule cycle rather than an equation, so no substitution can
; merge the reads and the unsat is reachable only through the congruence
; axiom -- refinement must fire.
; RUN: %solver --incremental --array-equality %s | %OutputCheck %s
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 4) (_ BitVec 32)))
(declare-fun c () (Array (_ BitVec 4) (_ BitVec 32)))
(declare-fun d () (Array (_ BitVec 4) (_ BitVec 32)))
(declare-fun p () Bool)
(declare-fun i () (_ BitVec 4))
(declare-fun j () (_ BitVec 4))
(assert p)
(assert (or p (= c d)))
(assert (= ((_ extract 0 0) (select a i)) #b1))
(assert (= ((_ extract 0 0) (select a j)) #b0))
; satisfiable while the indices may differ
; CHECK: ^sat
(check-sat)
(push 1)
(assert (bvule i j))
(assert (bvule j i))
; CHECK: ^unsat
(check-sat)
(pop 1)
; and satisfiable again once the index cycle is popped
; CHECK: ^sat
(check-sat)
