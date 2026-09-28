; x >=u ((t << 1) >> (t << s)), where t = x udiv s. This is UDIV15,
; the highest-firing division fact left out of the first port. Its nested
; variable shift is also the end-to-end check for the generic left barrel
; shifter added to express it.
;
; The assertion is exactly the negation of the fact. With a 256-bit quotient
; abstraction, installing that fact should decide the query without falling
; through to an exact divider.
; RUN: %solver -s --uninterpreted-functions --array-equality --uf-ackermann=auto --bv-term-abstraction=1 --bv-term-abstraction-schema-groups=udiv15 %s 2>&1 | %OutputCheck %s
; CHECK: BV abstraction: BVDIV dividend-above-shifted-double-quotient lemma
; CHECK-NEXT: BV abstraction: refined 1 operations
; CHECK: ^unsat$
;
; What this one fact costs is 229,374 clauses at this width -- three barrel
; shifters -- which is the number the schema-cost total exists to report and
; used to report as nothing. It is checked on quotient-not-negated-and.smt2
; rather than here: this leg is already the slowest in the suite at five
; seconds, and the property does not need the most expensive fact to
; demonstrate it.
;
; There is no exact control leg here, and there cannot be an affordable one:
; the assertion is the negation of the fact, so anything that does not install
; the fact has to prove a 256-bit divider unsatisfiable, which does not finish.
; What this leg establishes is that the fact is offered, named and applied end
; to end at a realistic width -- not that it is true. That is established by
; BVAbstractionLemma_Test, which checks every fact against the operation
; exhaustively below seven bits, by sampling at eight through sixty-four, and
; against the circuit STP blasts for the operation itself.
(set-logic QF_UFBV)
(declare-fun x () (_ BitVec 256))
(declare-fun s () (_ BitVec 256))
(assert
  (let ((t (bvudiv x s)))
    (bvult x (bvlshr (bvshl t (_ bv1 256)) (bvshl t s)))))
(check-sat)
(exit)
