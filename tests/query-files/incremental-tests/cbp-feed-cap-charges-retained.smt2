; The cross-level CBP feed cap bounds what the engine RETAINS for the live
; stack, so it must be charged the nodes a level ADDS, not the nodes it spans.
;
; Every level here is a comparison against the same product cone. The cone is
; one interned subgraph: the engine visits it on the first feed and stops at it
; on every feed after (extendParentMap halts at depsVisited), so five levels
; retain eight nodes and change, not five times eight. Charging each level its
; whole DAG size billed that one cone once per level, and a stack that shares
; structure -- which is what a pushed level normally is -- exhausted a cap it
; was nowhere near. Two levels in, this session read 24 against a true 9.
;
; The cap is set between the two measures: retention fits inside it, the sum
; does not. Under the old accounting the deeper levels are refused and CBP
; goes off, so the last check reports no fed level at all.
; RUN: %solver --incremental --incremental-profile --incremental-cbp-feed-cap 20 --check-sanity %s 2>&1 | %OutputCheck %s
; RUN: %solver --incremental-auto-engage-at 1 --incremental-profile --incremental-cbp-feed-cap 20 --check-sanity %s 2>&1 | %OutputCheck %s
(set-logic QF_BV)
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
(declare-fun c () (_ BitVec 8))
(assert (bvult (bvmul (bvadd a b) (bvadd a c)) #x40))
(push 1)
(assert (bvugt (bvmul (bvadd a b) (bvadd a c)) #x01))
; the base and the first pushed level are the cone plus one comparison
; CHECK: check=1 .*cbp-fed-levels=2 .*cbp-fed-nodes=8
(check-sat)
(push 1)
(assert (bvugt (bvmul (bvadd a b) (bvadd a c)) #x02))
; each further level adds its own comparison and nothing else
; CHECK: check=2 .*cbp-fed-levels=1 .*cbp-fed-nodes=1
(check-sat)
(push 1)
(assert (bvugt (bvmul (bvadd a b) (bvadd a c)) #x03))
; CHECK: check=3 .*cbp-fed-levels=1 .*cbp-fed-nodes=1
(check-sat)
(push 1)
(assert (bvugt (bvmul (bvadd a b) (bvadd a c)) #x04))
; still fed: retention is 11, well inside the cap of 20
; CHECK: check=4 .*cbp-fed-levels=1 .*cbp-fed-nodes=1 .*cbp-feed-rejected=0
(check-sat)
(exit)
