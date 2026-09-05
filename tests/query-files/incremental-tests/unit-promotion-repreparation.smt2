; Unit promotion must revalidate the form it PINNED, not the raw conjunction.
;
; A level promoted to permanent units is skipped by every later solve. The
; guard for that skip compared the level's raw conjunction, but the units
; came from its prepared form -- and the two diverge exactly when later
; content retracts a private elimination: the level re-prepares with its
; defining equation restored, that stronger form is encoded and then dropped
; by the skip, and the older units keep the variable unconstrained.
;
; The floating-point conjunct retires trail reuse on the first solve, which
; is promotion's precondition. recogniseDefinition refuses the BVNOT-headed
; equation, so the pushed-definition context never carries p and cannot
; repair the hole; the nested multiplication keeps constant-bit propagation
; from re-deriving the lost fact, which is what masks this at default flags.
; The last level then names p, making it non-private.
;
; The reset-oracle and CBP-off runs pin that neither mechanism is what makes
; the answer right.
; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --disable-cbitp %s | %OutputCheck %s
; RUN: %solver --check-sanity %s | %OutputCheck %s
(set-logic QF_BVFP)
(declare-fun fx () Float32)
(declare-fun fy () Float32)
(assert (fp.lt fx fy))
(declare-fun p () (_ BitVec 8))
(declare-fun t () (_ BitVec 8))
(declare-fun w () (_ BitVec 8))
(push 1)
(assert (and (= (bvnot p) (bvmul t (bvmul t t))) (bvult w #x80)))
(push 1)
(assert (bvult w #x10))
(check-sat)
(pop 1)
(push 1)
(assert (bvult w #x11))
(check-sat)
(pop 1)
(push 1)
(assert (bvult w #x12))
(check-sat)
(pop 1)
(push 1)
(assert (bvult w #x13))
(check-sat)
(pop 1)
(push 1)
(assert (bvult w #x14))
(check-sat)
(pop 1)
(push 1)
(assert (bvult w #x15))
(check-sat)
(pop 1)
(push 1)
(assert (bvult w #x16))
(check-sat)
(pop 1)
(push 1)
(assert (bvult w #x17))
(check-sat)
(pop 1)
(push 1)
(assert (bvult w #x18))
(check-sat)
(pop 1)
(push 1)
(assert (bvult w #x19))
(check-sat)
(pop 1)
(push 1)
(assert (bvult w #x1a))
(check-sat)
(pop 1)
(push 1)
(assert (bvult w #x1b))
(check-sat)
(pop 1)
(push 1)
(assert (bvult w #x1c))
(check-sat)
(pop 1)
(push 1)
(assert (bvult w #x1d))
(check-sat)
(pop 1)
(push 1)
(assert (bvult (bvadd p (bvmul t (bvmul t t))) #xff))
; the churn rounds are all sat, so this is the file's only unsat
; CHECK: ^unsat
(check-sat)
(exit)
