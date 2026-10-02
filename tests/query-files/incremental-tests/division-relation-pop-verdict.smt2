; RUN: %solver --incremental=on --bv-eq-abstraction=1 --bv-abstraction-width=8 --bb.div-by-const-width=8 %s | %OutputCheck %s
; RUN: %solver --incremental=on --ackermanize --bv-eq-abstraction=1 --bv-abstraction-width=8 --bb.div-by-const-width=8 %s | %OutputCheck %s
; RUN: %solver --incremental-auto-engage-at=1 -d --bv-eq-abstraction=1 --bv-abstraction-width=8 --bb.div-by-const-width=8 %s | %OutputCheck %s
; RUN: %solver -d --bv-eq-abstraction=1 --bv-abstraction-width=8 --bb.div-by-const-width=8 %s | %OutputCheck %s
;
; A division by a constant is encoded through its defining relation over
; fresh quotient and remainder inputs. The equality abstraction registers
; a proxy vector for the quotient the first time the term is an operand,
; and the registry answers with that vector for every later root. The
; relation used to be conjoined into the root that minted it alone: once
; the first level is popped, the second level re-mints the pair, the
; registry still names the first one, and the refined equality is over a
; free quotient. The second query answered sat; the truth is unsat, since
; x / 7 times 7 never exceeds x.
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(declare-fun v () (_ BitVec 8))
(declare-fun z () (_ BitVec 8))
(declare-fun w () (_ BitVec 8))
(push 1)
(assert (= (bvand y v) (bvudiv x #x07)))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (= (bvand z w) (bvudiv x #x07)))
(assert (bvugt (bvmul (bvand z w) #x07) x))
; CHECK-NEXT: ^unsat
(check-sat)
(pop 1)
