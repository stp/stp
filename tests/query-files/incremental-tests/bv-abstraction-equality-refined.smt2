; The driver refines the equality abstraction it asked the blaster to make.
;
; --bv-eq-abstraction replaces an equality by a free Boolean and leaves it to
; a CEGAR loop to pin the Boolean to the operands' bits once a candidate shows
; the two disagree. The persistent driver bit-blasts through the same blaster
; and so got the same free Booleans, and it had no such loop: nothing ever
; compared the Boolean against the bits, and the candidate the solver returned
; was published as a model.
;
; What that produced here is a model of a one-line query in which two
; variables asserted to differ are both zero. -d makes the driver re-evaluate
; the raw assertion stack against the model it built, which is the check that
; caught it:
;
;   Fatal Error: IncrementalSolver: the model does not satisfy an asserted
;   formula
;
; -- and without -d there was no diagnostic at all, just the wrong model.
;
; The second leg is the control: the verdict and the model belong to the
; query, not to the encoding that reached them.
;
; RUN: %solver --incremental=on -d --bv-eq-abstraction=1 --bv-abstraction-width=1 %s 2>&1 | %OutputCheck --check-prefix=ABSTRACTED %s
; RUN: %solver --incremental=off -d --bv-eq-abstraction=1 --bv-abstraction-width=1 %s 2>&1 | %OutputCheck --check-prefix=PLAIN %s
;
; ABSTRACTED-NOT: Fatal Error
; ABSTRACTED-NOT: Assertion
; ABSTRACTED: ^sat$
;
; PLAIN: ^sat$
;
(set-logic QF_BV)
(declare-const x0 (_ BitVec 1))
(declare-const x2 (_ BitVec 1))
(assert (distinct x0 x2))
(check-sat)
(exit)
