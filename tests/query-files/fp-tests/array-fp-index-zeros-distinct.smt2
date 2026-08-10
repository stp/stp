; RUN: %solver %s | %OutputCheck %s
;
; The index quotient must collapse exactly the NaNs and nothing else:
; SMT-LIB '=' keeps +0 and -0 distinct values, so a float-indexed array has
; a cell for each, and they can hold different bitvectors. An
; overenthusiastic canonicalisation (fp.eq rather than '=') would merge the
; two cells and answer unsat.
(set-logic QF_ABVFP)
(declare-fun a () (Array (_ FloatingPoint 8 24) (_ BitVec 8)))
(assert (= (select a (fp #b0 #b00000000 #b00000000000000000000000)) #x01))
(assert (= (select a (fp #b1 #b00000000 #b00000000000000000000000)) #x02))
; CHECK: ^sat
(check-sat)
