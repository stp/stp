; The same for the term abstraction: a comparison the driver abstracted is a
; comparison the driver has to refine.
;
; --bv-term-abstraction replaces a comparison by a free Boolean, and under the
; persistent driver nothing pinned it, so the solver was free to satisfy
; (bvslt x0 x2) by setting the Boolean rather than by choosing the operands.
; -d re-evaluated the raw stack against the resulting model and rejected it:
;
;   Fatal Error: IncrementalSolver: the model does not satisfy an asserted
;   formula
;
; Two bits is the floor for this: at one bit the comparison is below the
; abstraction's width, and nothing is abstracted at all.
;
; RUN: %solver --incremental=on -d --bv-term-abstraction=1 --bv-abstraction-width=1 %s 2>&1 | %OutputCheck --check-prefix=ABSTRACTED %s
; RUN: %solver --incremental=off -d --bv-term-abstraction=1 --bv-abstraction-width=1 %s 2>&1 | %OutputCheck --check-prefix=PLAIN %s
;
; ABSTRACTED-NOT: Fatal Error
; ABSTRACTED-NOT: Assertion
; ABSTRACTED: ^sat$
;
; PLAIN: ^sat$
;
(set-logic QF_BV)
(declare-const x0 (_ BitVec 2))
(declare-const x2 (_ BitVec 2))
(assert (bvslt x0 x2))
(check-sat)
(exit)
