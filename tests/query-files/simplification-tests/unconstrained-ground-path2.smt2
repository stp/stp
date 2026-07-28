; RUN: %solver %s | %OutputCheck %s
; CHECK: ^unsat
(set-logic QF_BV)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status unsat)

; Only one polarity is achievable: (bvurem x 100) < 100 < 200, so the
; equality is plain false. The ground-path collapse must NOT fire here
; (it is purely under-approximating and does no constant folding); the
; formula stays for the rest of the pipeline, and the final answer must
; be unsat.
(declare-fun x () (_ BitVec 128))
(assert (= (bvurem x (_ bv100 128)) (_ bv200 128)))

(check-sat)
(exit)
