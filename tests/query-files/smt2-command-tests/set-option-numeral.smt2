; The three standard options that take a numeral rather than a string or a
; boolean. These used to be syntax errors that abandoned the script; now they
; parse and, since STP does not act on any of them, answer "unsupported".
; RUN: %solver %s | %OutputCheck %s
; CHECK: ^unsupported
(set-option :verbosity 0)
; CHECK-NEXT: ^unsupported
(set-option :random-seed 42)
; CHECK-NEXT: ^unsupported
(set-option :reproducible-resource-limit 100)
(set-logic QF_BV)
(declare-fun x () (_ BitVec 4))
(assert (= x #x1))
; CHECK-NEXT: ^sat
(check-sat)
