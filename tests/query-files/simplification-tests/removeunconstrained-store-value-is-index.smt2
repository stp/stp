; RUN: %solver -d %s | %OutputCheck %s
; RUN: %solver -d --incremental %s | %OutputCheck %s
; CHECK: ^sat
;
; Regression test for RemoveUnconstrained's write rule over a store whose
; written value is also its index. In (store b s0 s0) both b and s0 have
; the store as their only parent -- parents are counted once, however many
; times they name a child -- so both looked unconstrained and the rule
; replaced the store with a fresh array v, defining b := v and s0 := v[s0].
; That definition reads s0 to find s0. The incremental driver's model check
; evaluates the original formula, followed the definition round forever,
; and never answered. The rule must not fire when the value is the index.
(set-logic QF_AUFBV)
(declare-sort S 0)
(declare-fun s0 () S)
(declare-fun s1 () S)
(declare-fun f (S) S)
(declare-fun b () (Array S S))
(assert (= s1 (select (store b s0 s0) (f s1))))
(check-sat)
