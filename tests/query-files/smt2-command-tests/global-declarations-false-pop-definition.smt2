; The same rule covers definitions, not just declarations: with
; :global-declarations false a define-fun made inside an assertion level goes
; away with it. A definition whose body mentions a symbol from the same level
; must not keep that symbol -- or itself -- alive past the pop.
; RUN: not %solver %s | %OutputCheck %s
(set-option :global-declarations false)
(set-logic QF_BV)
(push 1)
(declare-fun x!1 () Bool)
(define-fun x!2 () Bool (not x!1))
(pop 1)
; CHECK: .*error.*token: x!2.*
(assert (not x!2))
(check-sat)
