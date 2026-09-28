; The abstraction records outlive a check-sat, and so must their refinement.
;
; The driver keeps one bit-blast and one SAT solver across the whole session,
; so the abstractions it harvests accumulate and the clauses pinning them are
; permanent -- each says only what an abstraction variable means in terms of
; AIG bits the encoding already carries, which is true under any set of
; assumptions and survives every push and pop. This walks a session over both
; abstraction families and both verdicts to pin that: five checks, two of them
; inside pushed scopes that are then popped, with an assertion added after the
; last pop so the final check is a stack no earlier one solved.
;
; The two legs answer the same five things, which is the property that
; matters; -d re-derives each model against the raw stack, so a sat here is a
; model and not just a line.
;
; RUN: %solver --incremental=on --array-equality -d --bv-eq-abstraction=1 --bv-term-abstraction=1 --bv-abstraction-width=1 %s 2>&1 | %OutputCheck --check-prefix=ABSTRACTED %s
; RUN: %solver --incremental=on --array-equality -d %s 2>&1 | %OutputCheck --check-prefix=PLAIN %s
;
; ABSTRACTED-NOT: Fatal Error
; ABSTRACTED-NOT: Assertion
; ABSTRACTED: ^sat$
; ABSTRACTED-NEXT: ^unsat$
; ABSTRACTED-NEXT: ^sat$
; ABSTRACTED-NEXT: ^sat$
; ABSTRACTED-NEXT: ^sat$
;
; PLAIN: ^sat$
; PLAIN-NEXT: ^unsat$
; PLAIN-NEXT: ^sat$
; PLAIN-NEXT: ^sat$
; PLAIN-NEXT: ^sat$
;
(set-logic QF_ABV)
(declare-const a (Array (_ BitVec 3) (_ BitVec 4)))
(declare-const b (Array (_ BitVec 3) (_ BitVec 4)))
(declare-const i (_ BitVec 3))
(declare-const x (_ BitVec 4))
(assert (= (store a i x) b))
(check-sat)
(push 1)
; b holds x at i by construction, so this cannot hold with it.
(assert (distinct (select b i) x))
(check-sat)
(pop 1)
(check-sat)
(push 1)
(assert (bvult x (select a i)))
(check-sat)
(pop 1)
; The two arrays differ exactly where the store landed, which needs a to have
; held something else there.
(assert (distinct a b))
(check-sat)
(exit)
