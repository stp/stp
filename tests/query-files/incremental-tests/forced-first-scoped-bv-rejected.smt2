; A scoped first-stack trial which does not halve the DAG must commit neither
; its exact-stack block nor model definitions.  This tiny XOR cycle is below
; the policy's cliff-sized input floor (and also has no pure polarity), so the
; ordinary per-level path answers the check and retains its normal roots/search
; shape.
; RUN: %solver --incremental --incremental-profile --check-sanity %s 2>&1 | %OutputCheck %s
(set-option :produce-models true)
(set-logic QF_BV)
(declare-fun p () Bool)
(declare-fun q () Bool)
(declare-fun r () Bool)
(declare-fun s () Bool)
(push 1)
(assert (and (xor p q) (xor q r) (xor r s) (xor s p)))
; CHECK: Incremental profile cbp/backend: check=1 .*cbp-fed-levels=2 .*extensionality=0 first-stack-preprocesses=0 first-stack-eliminations=0 first-stack-rejected=1
; CHECK: ^sat
(check-sat)
(get-value (p q))
(pop 1)
(exit)
