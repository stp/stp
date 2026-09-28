; (distinct (f a) (f b) (f c)) is ordered by chaining a, b and c.
;
; The operands are applications, so they are not the interchangeable thing --
; the arguments are. Permuting the arguments' values permutes the operand
; multiset and leaves f alone, so the formula maps to itself; and because the
; operands are pairwise different, so are the arguments, which is what makes
; some permutation of them increasing. What that buys is not a smaller
; encoding but a refinement loop that ends: with a hundred applications the
; checker takes 263 rounds to discover an assignment of arguments it could
; have been handed, and one round after it is.
;
; The clique stays. An order on the arguments implies nothing about the
; results unless f is injective, and whether f is injective is the question
; being asked -- so unlike the variable form, this one adds rather than
; replaces, and the counted group is the same either way.
;
; Three ways to not be this shape, one block each. An argument compared
; outside the distinct is no longer interchangeable, and ordering it would
; contradict that comparison. Two declarations mean permuting the arguments
; does not permute the operands. And under a negation the added chain makes
; the assertion weaker, so a model of the result need not be a model of the
; input.
;
; RUN: %solver --uninterpreted-functions --incremental=off -s %s 2>&1 | %OutputCheck %s
; CHECK: Ordered 1 symmetric distinct group\(s\)
; CHECK: ^sat
; CHECK: APPLIED-DONE
; CHECK-NOT: Ordered
; CHECK: ^sat
; CHECK: LEAKED-DONE
; CHECK-NOT: Ordered
; CHECK: ^sat
; CHECK: MIXED-DONE
; CHECK-NOT: Ordered
; CHECK: ^sat
;
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
(declare-const c (_ BitVec 8))
(assert (distinct (f a) (f b) (f c)))
(check-sat)
(echo "APPLIED-DONE")
(reset)
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
(declare-const c (_ BitVec 8))
(assert (distinct (f a) (f b) (f c)))
(assert (bvult b a))
(check-sat)
(echo "LEAKED-DONE")
(reset)
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-fun g ((_ BitVec 8)) (_ BitVec 8))
(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
(declare-const c (_ BitVec 8))
(assert (distinct (f a) (g b) (f c)))
(assert (bvult c a))
(check-sat)
(echo "MIXED-DONE")
(reset)
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
(declare-const c (_ BitVec 8))
(assert (not (distinct (f a) (f b) (f c))))
(check-sat)
