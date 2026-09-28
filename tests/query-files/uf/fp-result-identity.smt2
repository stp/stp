; = and fp.eq disagree on a floating-point UF result, and both answers have
; to be right.
;
; = is identity of values and is reflexive, so a result cannot differ from
; itself whatever it is -- including NaN. fp.eq is IEEE equality, which is
; false at NaN, so a result is not obliged to be fp.eq to itself. A result
; symbol encoded so that = and fp.eq coincided would get one of these wrong.
;
; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: ^unsat
; CHECK: ^sat
; CHECK: ^unsat
; CHECK: REACHED-END
;
(set-logic QF_UFBVFP)
(declare-fun q ((_ BitVec 4)) (_ FloatingPoint 8 24))
(declare-fun p (Bool) Bool)
(declare-const i (_ BitVec 4))
(push 1)
(assert (distinct (q i) (q i)))
(check-sat)
(pop 1)
(push 1)
(assert (not (fp.eq (q i) (q i))))
(check-sat)
(pop 1)
(push 1)
; The Bool-codomain companion, for the same reflexivity property on a sort
; with no NaN in it.
(assert (distinct (p true) (p true)))
(check-sat)
(pop 1)
(echo "REACHED-END")
