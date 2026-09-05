; RUN: %solver %s | %OutputCheck %s
;
; A float-indexed array follows SMT-LIB '=' on its indexes, and '=' makes
; every NaN one value: a cell stored at one NaN literal is read back at any
; other, whatever the payload or sign bits of either spelling. Raw-bit
; indexing would treat the two literals as different cells and answer sat.
; (Float constants intern NaN-canonically, so this holds even in the
; node-creation-time read-over-write simplification; the symbolic-index
; sibling test exercises the solve-time canonicalisation instead.)
(set-logic QF_ABVFP)
(declare-fun a () (Array (_ FloatingPoint 8 24) (_ BitVec 8)))
(assert (distinct (select (store a (fp #b0 #b11111111 #b10000000000000000000001) #x2a)
                          (fp #b1 #b11111111 #b00000000000000000000111))
                  #x2a))
; CHECK: ^unsat
(check-sat)
