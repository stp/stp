; RUN: %solver --SMTLIB2 --lra-float-driver 1 %s | %OutputCheck %s
;
; A query that declares a Real function and never applies it. There is no Real
; atom to assert, so the float driver's trail stays empty for the whole solve
; -- and syncFloatTrailIntoExact treated an empty trail as "already mirrored"
; and returned Clean without pushing. Pushing is what opens a candidate on the
; exact core, and the core answers check() only with one open, so the final
; check got InternalError back. The adapter then stopped the solve context,
; and a query whose Real content is nothing at all came back SOLVER_ERROR --
; through the C interface, a raw -100 on a boundary documented to answer
; 0, 1, 2 or 3.
;
; Reduced by delta debugging from a murxla trace. The Boolean chain is what
; makes the search reach a complete model with the propagator engaged, which
; is where the final check runs; sat is the exact core's own answer for this,
; and the point is that turning the float driver on does not change it.
; CHECK-NEXT: ^sat$
(set-logic QF_UFLRA)
(declare-const _x0 Bool)
(declare-fun _x5 (Bool) Bool)
(declare-fun _x6 (Real) Real)
(assert (_x5 (_x5 (_x5 (_x5 (_x5 (_x5 (_x5 (_x5 (_x5 (=> (_x5 (_x5 (_x5 (_x5 (_x5 (_x5 (_x5 (_x5 (_x5 (_x5 (_x5 false))))))))))) (_x5 (_x5 (_x5 (_x5 _x0)))))))))))))))
(check-sat)
(exit)
