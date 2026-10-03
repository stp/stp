; An abstraction's operand proxy means its term only under a root that ties
; it to that root's bits for the term.
;
; An abstracted equality reads its operands through proxy inputs, registered
; one vector per node because refinement resolves a record's operands through
; the registry by node, so every live record has to agree on one vector. Each
; proxy was tied to the operand's bits by a biconditional the driver asserted
; as a permanent unit, on the argument that a fresh variable defined by a
; circuit over the query's inputs constrains no assignment.
;
; A square root is not that circuit. It is encoded through a defining
; relation over fresh inputs which only the root that minted it conjoins, and
; BBForm re-mints the pair on every root for exactly that reason. So the
; first level mints the relation under its own literal and pins the proxy to
; those bits for the session; the second level re-mints the relation, asks
; the registry for the operand and gets the first level's proxy, now tied to
; inputs nothing constrains. The refined equality then says nothing about the
; square root, and the second query answered sat -- the wrong verdict
; outright, under both backends, with no self-check needed to see it.
;
; The second query bounds x in [4, 9), so sqrt x lies in [2, 3) and its IEEE
; encoding is at least 0x40000000. Requiring it to be less is unsatisfiable.
; RUN: %solver --incremental=on --bv-eq-abstraction=1 --bv-abstraction-width=8 %s | %OutputCheck %s
; RUN: %solver --incremental-auto-engage-at=1 --bv-eq-abstraction=1 --bv-abstraction-width=8 %s | %OutputCheck %s
; RUN: %solver --incremental=on --ackermanize --bv-eq-abstraction=1 --bv-abstraction-width=8 %s | %OutputCheck %s
; RUN: %solver --incremental=on -d --bv-eq-abstraction=1 --bv-abstraction-width=8 %s | %OutputCheck %s
(set-logic QF_BVFP)
(declare-fun x () Float32)
(declare-fun y () (_ BitVec 32))
(declare-fun v () (_ BitVec 32))
(declare-fun z () (_ BitVec 32))
(declare-fun w () (_ BitVec 32))
(push 1)
(assert (= (bvand y v) (fp.to_ieee_bv (fp.sqrt RNE x))))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (= (bvand z w) (fp.to_ieee_bv (fp.sqrt RNE x))))
(assert (fp.geq x ((_ to_fp 8 24) RNE 4.0)))
(assert (fp.lt x ((_ to_fp 8 24) RNE 9.0)))
(assert (bvult (bvand z w) #x40000000))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
