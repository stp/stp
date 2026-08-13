; The sharing-aware flattening stack (--flattening, --common-subsum,
; --pair-extract) is on by default, can be switched off individually, and
; --disable-simplifications switches all of it off.

; RUN: %solver --help 2>&1 | %OutputCheck %s --check-prefix=HELP
; HELP: --flattening BOOLEAN \[1\]
; HELP: --common-subsum BOOLEAN \[1\]
; HELP: --pair-extract BOOLEAN \[1\]

; RUN: %solver %s | %OutputCheck %s --check-prefix=SOLVE
; RUN: %solver --flattening 0 --common-subsum 0 --pair-extract 0 %s | %OutputCheck %s --check-prefix=SOLVE
; RUN: %solver --disable-simplifications %s | %OutputCheck %s --check-prefix=SOLVE

; SOLVE: ^unsat$

; The two additions share the sub-sum x + y + z, so common sub-sum
; extraction has something to factor when it runs.
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(declare-fun z () (_ BitVec 8))
(assert (= (bvadd x y z) (_ bv10 8)))
(assert (= (bvadd x y z (_ bv1 8)) (_ bv10 8)))
(check-sat)
(exit)
