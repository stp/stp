; The UF+FP logic names. Without them no query can name a logic that admits
; both uninterpreted functions and the floating-point keywords: outside an FP
; logic "RoundingMode" is not a token at all, so a signature naming it is a
; plain syntax error rather than a UF diagnostic (see smt2.lex's
; SMT2SetFloatTokens gate).
;
; Each logic is accepted, turns the floating-point keywords on, and admits a
; UF declaration without a separate command-line switch. The LRA suffix does
; not change that classification.
;
; QF_AUFBVFP is the SMT-LIB spelling -- the theory letters go A, UF, BV, FP,
; which is the order QF_AUFBV already uses here. QF_UFABVFP is the spelling
; this branch shipped first and stays accepted as an alias for it, as does its
; FPLRA counterpart.
;
; RUN: %solver --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK-NOT: Wrong input logic
; CHECK: ^unsat
; CHECK: ^unsat
; CHECK: ^unsat
; CHECK: ^unsat
; CHECK: ^unsat
; CHECK: ^unsat
; CHECK: ^unsat
; CHECK: ^unsat
; CHECK: REACHED-END
;
(set-logic QF_UFFP)
(declare-fun kf (RoundingMode) RoundingMode)
(assert (distinct (kf RNE) (kf RNE)))
(check-sat)
(reset)
(set-logic QF_UFBVFP)
(declare-fun kb ((_ BitVec 4)) RoundingMode)
(assert (distinct (kb #x0) (kb #x0)))
(check-sat)
(reset)
(set-logic QF_UFABVFP)
(declare-fun ka ((_ BitVec 4)) RoundingMode)
(declare-const a (Array (_ BitVec 4) (_ BitVec 4)))
(assert (distinct (ka (select a #x0)) (ka (select a #x0))))
(check-sat)
(reset)
(set-logic QF_AUFBVFP)
(declare-fun kc ((_ BitVec 4)) RoundingMode)
(declare-const c (Array (_ BitVec 4) (_ BitVec 4)))
(assert (distinct (kc (select c #x0)) (kc (select c #x0))))
(check-sat)
(reset)
(set-logic QF_UFFPLRA)
(declare-fun lf (RoundingMode) RoundingMode)
(assert (distinct (lf RNE) (lf RNE)))
(check-sat)
(reset)
(set-logic QF_UFBVFPLRA)
(declare-fun lb ((_ BitVec 4)) RoundingMode)
(assert (distinct (lb #x0) (lb #x0)))
(check-sat)
(reset)
(set-logic QF_UFABVFPLRA)
(declare-fun la ((_ BitVec 4)) RoundingMode)
(declare-const d (Array (_ BitVec 4) (_ BitVec 4)))
(assert (distinct (la (select d #x0)) (la (select d #x0))))
(check-sat)
(reset)
(set-logic QF_AUFBVFPLRA)
(declare-fun lc ((_ BitVec 4)) RoundingMode)
(declare-const e (Array (_ BitVec 4) (_ BitVec 4)))
(assert (distinct (lc (select e #x0)) (lc (select e #x0))))
(check-sat)
(echo "REACHED-END")
