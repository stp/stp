; REQUIRES: cadical-3
;
; Here rather than beside the lra-* files because it names its backend, and
; those are swept with each backend's flag prepended.
;
; --lra-extension-restart-sat copies the formula into a fresh CaDiCaL, which
; CaDiCaL cannot do once bounded variable addition (factor) is on, or while
; the array index hints hold its propagator slot. These were accepted and
; then failed the query with SOLVER_ERROR at its first UF refinement; an
; explicit request for either is now refused up front.
; RUN: not %solver --SMTLIB2 --cadical --cadical-factor=on --lra-extension-restart-sat=1 %s 2>&1 | %OutputCheck --check-prefix=FACTOR %s
; RUN: not %solver --SMTLIB2 --cadical --array-index-hints=decide --lra-extension-restart-sat=1 %s 2>&1 | %OutputCheck --check-prefix=HINTS %s
;
; The array reads survive to the solver (more than Ackermannisation takes),
; so a Real solve's default factor, 'auto', would turn factor on here. With
; the reset asked for it is off instead, and the reset runs. The
; array-index-hints sweep prepends 'decide', hence the explicit 'off'.
; RUN: %solver --SMTLIB2 --cadical --array-index-hints=off --lra-extension-restart-sat=1 -s %s 2>&1 | %OutputCheck --check-prefix=RESET %s
; RUN: %solver --SMTLIB2 --cadical --array-index-hints=off --lra-extension-restart-sat=1 %s | %OutputCheck %s
; RUN: %solver --SMTLIB2 --cadical --array-index-hints=off --cadical-factor=auto --lra-extension-restart-sat=1 %s | %OutputCheck %s
; RUN: %solver --SMTLIB2 --cadical --array-index-hints=off --cadical-factor=off --lra-extension-restart-sat=1 %s | %OutputCheck %s
; RUN: %solver --SMTLIB2 --cadical --array-index-hints=phase --lra-extension-restart-sat=1 %s | %OutputCheck %s
; RUN: %solver --SMTLIB2 --cadical --cadical-factor=on --array-index-hints=decide --lra-extension-restart-sat=0 %s | %OutputCheck %s
;
; CHECK: ^unsat$
; RESET: "sat_search_resets":1
; FACTOR: ^ERROR: --lra-extension-restart-sat=1 requires --cadical-factor=off$
; FACTOR-NOT: ^(sat|unsat|unknown)$
; HINTS: ^ERROR: --lra-extension-restart-sat=1 cannot be combined with --array-index-hints=decide$
; HINTS-NOT: ^(sat|unsat|unknown)$
(set-logic QF_UFLRA)
(declare-sort U 0)
(declare-fun a () (Array U U))
(declare-fun f (Real) Real)
(declare-fun i0 () U)
(declare-fun i1 () U)
(declare-fun i2 () U)
(declare-fun i3 () U)
(declare-fun i4 () U)
(declare-fun i5 () U)
(declare-fun i6 () U)
(declare-fun i7 () U)
(declare-fun i8 () U)
(declare-fun i9 () U)
(declare-fun i10 () U)
(declare-fun i11 () U)
(declare-fun i12 () U)
(declare-fun i13 () U)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (distinct i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13))
(assert (not (= (select a i0) (select a i1))))
(assert (not (= (select a i1) (select a i2))))
(assert (not (= (select a i2) (select a i3))))
(assert (not (= (select a i3) (select a i4))))
(assert (not (= (select a i4) (select a i5))))
(assert (not (= (select a i5) (select a i6))))
(assert (not (= (select a i6) (select a i7))))
(assert (not (= (select a i7) (select a i8))))
(assert (not (= (select a i8) (select a i9))))
(assert (not (= (select a i9) (select a i10))))
(assert (not (= (select a i10) (select a i11))))
(assert (not (= (select a i11) (select a i12))))
(assert (not (= (select a i12) (select a i13))))
(assert (> (f x) (f y)))
(assert (<= x y))
(assert (>= x y))
(check-sat)
(exit)
