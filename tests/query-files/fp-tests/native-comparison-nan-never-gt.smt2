; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --disable-simplifications %s | %OutputCheck %s
; RUN: %solver --bb.fp-native-cmp=false %s | %OutputCheck %s
;
; fp.gt over leaf operands survives lowering and is bit-blasted natively
; (BBcompareFP); fp.isNaN still lowers through SymFPU. A NaN operand -- on
; either side, with ANY payload the SAT solver can pick -- must make the
; comparison false, so this cross-encoding formula is unsatisfiable. The
; native encoding tests the exponent and significand fields rather than a
; canonical NaN pattern; a payload-sensitive isNaN would make this sat.
; The third run proves the SymFPU path agrees.
;
; CHECK: ^unsat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(declare-fun z () (_ FloatingPoint 8 24))
(declare-fun w () (_ FloatingPoint 8 24))
(assert (or (and (fp.gt x y) (fp.isNaN x))
            (and (fp.gt z w) (fp.isNaN w))))
(check-sat)
(exit)
