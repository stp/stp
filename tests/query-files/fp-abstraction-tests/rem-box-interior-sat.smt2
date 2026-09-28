; RUN: %solver --fp-abstraction=true --fp-abstraction-ops=rem --fp-abstraction-box-lemmas=true %s | %OutputCheck %s
; RUN: %solver --fp-abstraction=true --fp-abstraction-ops=rem --fp-abstraction-box-lemmas=true --fp-abstraction-repair=false %s | %OutputCheck %s
; CHECK: ^sat$
;
; All four corners have result bits [31:15] = 0x07e74, but the exact
; interior witness xb=0x791b3fff, yb=0x3fd90000 has remainder 27/64,
; bits 0x3ed80000. A corner-prefix lemma for remainder wrongly proves UNSAT.
(set-logic QF_BVFP)
(declare-fun xb () (_ BitVec 32))
(declare-fun yb () (_ BitVec 32))
(assert (= ((_ extract 31 15) xb) (_ bv62006 17)))
(assert (= ((_ extract 31 15) yb) (_ bv32690 17)))
(assert (= (fp.rem ((_ to_fp 8 24) xb) ((_ to_fp 8 24) yb))
           ((_ to_fp 8 24) #x3ed80000)))
(check-sat)
