; RUN: %solver --produce-models %s | %OutputCheck %s
; RUN: %solver %s | %OutputCheck --check-prefix=DEFAULT %s
; RUN: not %solver --logic NONSENSE %s 2>&1 | %OutputCheck --check-prefix=LOGIC %s
;
; --produce-models is a flag, so the file after it is still the input (as a
; value option it swallowed the file name); the command line's default is
; off. --logic takes the logics set-logic accepts and no other name.
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(assert (= x #x03))
(check-sat)
(get-value (x))
; CHECK: ^sat
; CHECK-NEXT: ^\(
; CHECK-NEXT: #x03
; DEFAULT: ^sat
; DEFAULT-NEXT: ^unsupported
; LOGIC: --logic must be one of
