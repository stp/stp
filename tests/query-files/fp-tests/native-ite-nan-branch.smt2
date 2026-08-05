; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --disable-simplifications %s | %OutputCheck %s
; RUN: %solver --bb.fp-native-cmp=false %s | %OutputCheck %s
;
; When the condition holds, the mux is a NaN, and nothing is greater than a
; NaN -- so this formula is unsatisfiable. It pins the branch a true
; condition selects (swap the branches in the mux and it becomes sat, since
; the solver is then free to pick a large x), and it does so with a value
; the comparison itself treats specially. The NaN branch is spelled as a
; to_fp reinterpret of constant bits, the form literals actually arrive in,
; so the branch also exercises the constant lookthrough inside a mux.
;
; CHECK: ^unsat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun z () (_ FloatingPoint 8 24))
(declare-fun c () Bool)
(assert c)
(assert (fp.gt (ite c ((_ to_fp 8 24) #x7fc00001) x) z))
(check-sat)
(exit)
