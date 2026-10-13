; Post-order means an earlier sibling cannot see a label defined in a later
; one, and a term cannot name itself.
; RUN: not %solver %s 2>&1 | %OutputCheck %s
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
; CHECK: ^\(error "syntax error.*token: a"\)$
(assert (and a (! (= x #x2a) :named a)))
(check-sat)
