; A pushed definition whose substitution would rewrite INSIDE a
; floating-point operation is refused: the conjunct encodes raw-keyed,
; the definer equation stays asserted, and the raw circuit keeps its
; sharing with every other user (a generated variant-push family
; measured 0.3s raw against a deterministic 45s-to-timeout when each
; variant minted its own substituted symfpu circuits). A substitution
; that FOLDS the floating-point content away entirely is still adopted:
; that collapse is what the pushed harvest exists for.
; RUN: %solver --incremental -s %s 2>&1 | %OutputCheck %s
(set-logic QF_BVFP)
(declare-fun p () Bool)
(declare-fun q () Bool)
(declare-fun x () (_ FloatingPoint 8 24))
; base: an fp.add whose argument carries the flag; the raw circuit is
; the one every level must keep sharing (the base is never rewritten
; under pushed definitions)
(assert (fp.gt (fp.add RNE x (ite p (fp #b0 #x7f #b00000000000000000000000)
                                    (_ +zero 8 24)))
               (_ +zero 8 24)))
; refusal path, satisfiable: substituting p -> true into the fp.add
; would mint a novel variant circuit; refused, the definer still binds
(push 1)
(assert (= p true))
(assert (fp.lt x (fp #b0 #x82 #b01000000000000000000000)))
; CHECK: ^sat
(check-sat)
(pop 1)
; refusal path, unsatisfiable: the pushed conjunct names the SAME raw
; sum as the base; refusing the rewrite keeps it the same circuit, and
; the sum cannot be both above and below zero
(push 1)
(assert (= p false))
(assert (fp.lt (fp.add RNE x (ite p (fp #b0 #x7f #b00000000000000000000000)
                                    (_ +zero 8 24)))
               (_ +zero 8 24)))
; CHECK: ^unsat
(check-sat)
(pop 1)
; fold path: under q -> true every floating-point node of the pushed
; conjunct folds to a constant -- nothing novel reaches the blaster and
; the substitution is adopted
(push 1)
(assert (= q true))
(assert (fp.lt (ite q (fp #b0 #x7f #b00000000000000000000000)
                      (fp #b0 #x80 #b00000000000000000000000))
               (fp #b0 #x81 #b00000000000000000000000)))
; CHECK: ^sat
(check-sat)
(pop 1)
; identical re-push: the refused (raw-keyed) encodings are cache hits
(push 1)
(assert (= p true))
(assert (fp.lt x (fp #b0 #x82 #b01000000000000000000000)))
; CHECK: Incremental: encoded 0 new conjuncts, added 0 clauses
; CHECK: ^sat
(check-sat)
(pop 1)
(exit)
