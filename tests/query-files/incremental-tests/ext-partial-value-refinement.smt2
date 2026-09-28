; An extensionality round whose read-congruence refinement ranges over
; value symbols the block's cone only partially encoded: one bit of each
; 32-bit read is used, so the other 31 bits of the abstraction variables
; never reach the solver. The refinement machinery (getEquals) encodes
; congruence axioms straight over the registry symbols' bit variables,
; so every such symbol must be totalised -- given a fresh, unconstrained
; variable for each unused bit -- before the axioms are encoded. The ext
; round totalised only the consistency checker's symbols, never the
; round registry's rows: axioms were then built over missing-bit
; markers, which CaDiCaL's factor translation rejects with a crash, and
; every other backend consumes silently as a corrupted, meaningless
; axiom.
;
; The array equality over c and d only routes the rounds through the
; extensionality block; the congruence work is on a's two reads. The
; indices are equated through a bvule cycle, not a direct equation, so
; no substitution can merge the reads syntactically -- the unsat is
; reachable only through the congruence axiom, so refinement must fire.
; RUN: %solver --incremental --array-equality %s | %OutputCheck %s
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 4) (_ BitVec 32)))
(declare-fun c () (Array (_ BitVec 4) (_ BitVec 32)))
(declare-fun d () (Array (_ BitVec 4) (_ BitVec 32)))
(declare-fun i () (_ BitVec 4))
(declare-fun j () (_ BitVec 4))
(assert (= c d))
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
