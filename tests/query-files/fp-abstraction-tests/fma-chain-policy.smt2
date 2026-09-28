; RUN: %solver --fp-abstraction=true -s %s 2>&1 | %OutputCheck %s
; RUN: %solver --fp-abstraction=true --fp-abstraction-ops=mul,div,sqrt --fp-abstraction-chain-ops=fma -s %s 2>&1 | %OutputCheck --check-prefix=CHAIN %s
; RUN: %solver --fp-abstraction=true --fp-abstraction-ops=mul,div,sqrt -s %s 2>&1 | %OutputCheck --check-prefix=NOFMA %s
;
; Two fused multiply-adds: one over the product's result, one over inputs
; alone. By default the fma is in the operation set and both are records
; beside the product. As a chain operation -- abstracted only when an
; operand is the result of an application already abstracted -- the first
; is a record and the second is encoded exactly; and with neither, the
; product is the only record.
; CHECK: FpAbstraction: 3 abstracted \(0 shared occurrences, 3 candidates, 0 by chain\)
; CHECK: ^sat
; CHAIN: FpAbstraction: 2 abstracted \(0 shared occurrences, 2 candidates, 1 by chain\)
; CHAIN: ^sat
; NOFMA: FpAbstraction: 1 abstracted \(0 shared occurrences, 1 candidates, 0 by chain\)
; NOFMA: ^sat
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 24))
(declare-const y (_ FloatingPoint 8 24))
(declare-const z (_ FloatingPoint 8 24))
(declare-const w (_ FloatingPoint 8 24))
(assert (fp.isNormal x))
(assert (fp.isNormal y))
(assert (fp.isNormal z))
(assert (fp.isNormal w))
(assert (fp.lt (fp.fma RNE (fp.mul RNE x y) z w) (fp.fma RNE x z w)))
(check-sat)
