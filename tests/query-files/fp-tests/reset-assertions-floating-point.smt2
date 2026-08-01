; RUN: %solver %s | %OutputCheck %s
;
; reset-assertions switches one checker from FP to pure BV and back again.
; FP activation follows the live assertions, not the manager's construction
; history. Declarations are rebuilt after each reset because STP implements
; the default :global-declarations false.
(set-logic QF_BVFP)
(declare-const f (_ FloatingPoint 5 11))
(declare-const b (_ BitVec 8))

(assert (fp.isZero f))
(assert (fp.isNaN f))
; CHECK-NEXT: ^unsat
(check-sat)

(reset-assertions)
(declare-const b (_ BitVec 8))
(assert (= b #x2a))
; CHECK-NEXT: ^sat
(check-sat)

(reset-assertions)
(declare-const f (_ FloatingPoint 5 11))
(assert (fp.isNormal f))
; CHECK-NEXT: ^sat
(check-sat)
