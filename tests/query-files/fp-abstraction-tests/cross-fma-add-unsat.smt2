; RUN: %solver --fp-abstraction=true --fp-abstraction-ops=add,fma -s %s 2>&1 | %OutputCheck %s
;
; x*1 + z is x + z before either is rounded, so the fused multiply-add with
; a unit factor is the sum: one fact between the two records, and the
; query is unsat before any candidate is read. (A top-level (= y 1.0)
; would be substituted and the fma rewritten away before the abstraction
; sees it, so the unit factor is pinned by two bounds instead.)
; CHECK: FpAbstraction: 2 abstracted .* 1 cross-operation rules, .* 0 releases
; CHECK: ^unsat
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 11 53))
(declare-const y (_ FloatingPoint 11 53))
(declare-const z (_ FloatingPoint 11 53))
(assert (fp.leq ((_ to_fp 11 53) RNE 1.0) y))
(assert (fp.leq y ((_ to_fp 11 53) RNE 1.0)))
(assert (not (= (fp.fma RNE x y z) (fp.add RNE x z))))
(check-sat)
