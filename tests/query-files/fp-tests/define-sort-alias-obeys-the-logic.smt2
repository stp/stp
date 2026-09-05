; RUN: %solver %s | %OutputCheck %s
;
; The floating-point names are keywords only under an FP set-logic: QF_BV
; inputs legitimately declare symbols called "fp", "NaN" or "RNE", and parsed
; that way before floating-point support existed. Every such name goes through
; fpKeyword() in the lexer to enforce that.
;
; define-sort's body does not: SKIP_SEXPR swallows it and the grammar
; re-tokenises the raw text by hand, so it never meets those rules. It used to
; match "Float32" regardless of the logic, which let a QF_BV script obtain a
; FloatingPoint variable -- and get a model printed with the "fp" constructor
; while "fp" was also a bit-vector symbol the script had declared, in the same
; scope. It now answers "unsupported", as it does for every other sort it does
; not implement.
;
; The alias itself still works under an FP logic: see define-sort-alias.smt2.
; CHECK: ^unsupported
; CHECK-NEXT: ^sat
(set-logic QF_BV)
(define-sort MyFloat () Float32)
(declare-fun fp () (_ BitVec 8))
(assert (= fp #x01))
(check-sat)
