; RUN: %solver -d %s | %OutputCheck %s
;
; Regression: STP's counterexample checker (-d) re-evaluates the asserted
; formula against the model it built, walking every node with
; ComputeFormulaUsingModel. A rewrite of that evaluator dropped the cases for
; all floating-point predicate kinds, so a satisfiable query whose model was
; checked over one aborted:
;   FP_ISZERO Fatal Error: ComputeFormulaUsingModel: the kind has not been implemented
; The predicate reaches the checker only because it survives bit-blasting here:
; it is over an ((_ to_fp ..) bits) reinterpret kept inside an ite.
; (get-value cannot exercise this -- STP only get-values plain variables, and
; get-value does not re-evaluate the asserted formula; -d does.)
(set-logic QF_BVFP)
(declare-fun f () (_ BitVec 32))
(declare-fun x () (_ BitVec 23))
(declare-fun y () (_ BitVec 23))
(assert (fp.isZero (ite (not (= (bvuge x y)
                                (fp.eq ((_ to_fp 8 24) f) ((_ to_fp 8 24) f))))
                        (fp.max (_ +zero 8 24) (_ +zero 8 24))
                        ((_ to_fp 8 24) f))))
; CHECK: ^sat
(check-sat)
