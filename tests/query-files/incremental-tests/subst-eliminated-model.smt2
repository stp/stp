; Base-level definitional chains are substituted through before encoding --
; the variables may never reach the SAT solver at all -- but get-value must
; still answer for them, by evaluating their definitions.
; RUN: %solver --incremental --check-sanity %s | %OutputCheck %s
; RUN: %solver --incremental-auto-engage-at 1 --check-sanity %s | %OutputCheck %s
(set-option :produce-models true)
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(declare-fun p () Bool)
(assert (= x (bvadd y #x01)))
(assert (= y #x05))
(assert p)
(push 1)
(assert (= x #x06))
; CHECK-NEXT: ^sat
(check-sat)
; CHECK: \|x\| +#x06
; CHECK: \|y\| +#x05
(get-value (x y))
(pop 1)
(push 1)
; the chain still binds x = y + 1 = 6, so pinning x elsewhere is unsat
(assert (= x #x09))
; CHECK: ^unsat
(check-sat)
(pop 1)
; two definitions of the same variable must contradict, not shadow
(assert (= y #x07))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
