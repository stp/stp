; get-unsat-assumptions after check-sat-assuming: the driver assumes the
; assumption level one conjunct per root literal, so an unsat answer can
; name exactly the assumptions the refutation used. Terms print in their
; parsed, factory-rewritten form, the same convention get-value uses.
; RUN: %solver --incremental %s | %OutputCheck %s
; RUN: %solver --incremental-auto-engage-at 1 %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun p () Bool)
(assert (bvult x #x0a))
; a single contradictory assumption is the whole core
(check-sat-assuming ((bvugt x #x14)))
; CHECK: ^unsat
(get-unsat-assumptions)
; CHECK: ^\(\(bvugt \|x\|  #x14\)\)$
; two assumptions that are only jointly unsat: any correct core has both
(check-sat-assuming ((bvult x #x03) (bvugt x #x05)))
; CHECK: ^unsat
(get-unsat-assumptions)
; CHECK: ^\(\(bvugt  #x03 \|x\|\) \(bvugt \|x\|  #x05\)\)$
; an irrelevant assumption rides along and must not be reported
(check-sat-assuming ((bvugt x #x14) p))
; CHECK: ^unsat
(get-unsat-assumptions)
; CHECK: ^\(\(bvugt \|x\|  #x14\)\)$
; after a sat answer the core is empty
(check-sat-assuming ((bvult x #x05)))
; CHECK: ^sat
(get-unsat-assumptions)
; CHECK: ^\(\)$
; A native distinct is lowered for the persistent solver but retained for
; reporting. Matching the driver's failed conjunct back to the source
; assumption therefore has to use the same lowering, while printing the raw
; term still has to say `distinct`.
(check-sat-assuming ((bvult x #x02) (bvugt x #x00)
                     (distinct x #x01) p))
; CHECK: ^unsat
(get-unsat-assumptions)
; CHECK: ^\(\(bvugt  #x02 \|x\|\) \(not \(= \|x\|  #x00\)\) \(distinct \|x\|  #x01\)\)$
