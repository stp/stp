; One Boolean per abstracted predicate, not one per occurrence.
;
; The term families are canonicalised by the blaster: a second ask for a term
; it has already abstracted reuses the vector it registered, and the reason
; given for doing so is this driver. BBForm clears its memo on every new root,
; so two conjuncts sharing a subterm ask for it independently, and minting a
; second set of inputs for the second ask leaves two records over two sets that
; are free to disagree.
;
; Equalities and comparisons had the same exposure and none of the guard. Each
; occurrence minted a fresh Boolean and pushed a fresh record, so the same
; predicate was refined twice over two inputs -- and the refinement paid for
; both, once per occurrence, for the whole session.
;
; Here each predicate is written into two conjuncts, so the driver blasts each
; one twice. The coverage line counts operations on the left and records on the
; right, so one predicate abstracted once reads 1->1 -- and a second record for
; it reads 1->2, which is the shape of the defect: more records than there are
; operations to have them. Without the guard the equality leg reports exactly
; that.
;
; -d re-derives the answer under the published model, which is the check that
; matters if the reuse were wrong: a Boolean shared between two predicates that
; are not the same predicate would report sat on a model the raw stack rejects.
;
; RUN: %solver --incremental=on -d -t --bv-eq-abstraction=1 --bv-term-abstraction=1 %s 2>&1 | %OutputCheck --check-prefix=SHARED %s
; RUN: %solver --incremental=on -d %s 2>&1 | %OutputCheck --check-prefix=PLAIN %s
;
; SHARED: Abstraction coverage \(candidates -> abstracted\): eq=1->1 compare=1->1
; SHARED: ^sat$
;
; PLAIN: ^sat$
(set-logic QF_BV)
(declare-fun a () (_ BitVec 64))
(declare-fun b () (_ BitVec 64))
(declare-fun p () Bool)
(declare-fun q () Bool)
(assert (or p (= a b)))
(assert (or (not p) (= a b)))
(assert (or q (bvule a b)))
(assert (or (not q) (bvule a b)))
(check-sat)
(exit)
