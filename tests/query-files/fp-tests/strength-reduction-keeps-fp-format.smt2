; RUN: %solver %s | %OutputCheck %s
; CHECK: ^unsat
;
; Regression test for StrengthReduction dropping a floating-point
; constant's format.  Constant-bit analysis proves the bvumulo false, so
; the ite folds to the NaN literal while the tree is rebuilt.  The
; totally-fixed floating-point constant was then "replaced" by a plain
; bitvector constant of the same bits, which carries no exponent or
; significand widths.  Folding the enclosing fp.neg over that bare
; constant tried to build a floating-point constant of format (0, 0) and
; aborted with
;   Fatal Error: CreateFPSpecialConst: a floating-point format needs
;   nonzero exponent and significand widths
; The replacement must re-make the constant as a floating-point constant
; of the replaced node's format.  (fp.leq with a NaN operand is false,
; so the assertion is unsatisfiable.)
;
; Found by fuzzing with murxla; delta-minimized with ddSMT.
(set-logic QF_ABVFP)
(declare-const __ (_ BitVec 1))
(assert (fp.leq (_ NaN 11 53)
                (fp.neg (ite (not (bvumulo (_ bv0 11) ((_ zero_extend 10) __)))
                             (_ NaN 11 53)
                             (fp.rem (_ NaN 11 53) (_ NaN 11 53))))))
(check-sat)
