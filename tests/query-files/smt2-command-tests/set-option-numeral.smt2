; The three standard options that take a numeral rather than a string or a
; boolean. These used to be syntax errors that abandoned the script; now they
; parse. The seed is supported; the other two answer "unsupported".
; RUN: %solver %s | %OutputCheck %s
; CHECK: ^unsupported
(set-option :verbosity 0)
(set-option :random-seed 42)
; CHECK-NEXT: ^42$
(get-option :random-seed)
; CHECK-NEXT: ^unsupported
(set-option :reproducible-resource-limit 100)
(set-logic QF_BV)
(declare-fun x () (_ BitVec 4))
(assert (= x #x1))
; CHECK-NEXT: ^sat
(check-sat)
