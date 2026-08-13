; RUN: %solver --flattening=true -d %s | %OutputCheck %s
; CHECK-NEXT: ^sat
;
; The three conjuncts contain one another once the chainable equalities are
; expanded: each later assertion is an AND wrapping the previous one. When
; Flatten merges them into the top-level conjunction, its AND/OR duplicate
; filter drops every already-seen entry, so the rebuilt AND legitimately has
; *fewer* children than the original. An over-strong
; assert(Degree() <= newChildren.size()) aborted every assertions-enabled
; build on this input; found by murxla. -d checks the model against the
; original query, guarding against a conjunct genuinely going missing.
(declare-const _x0 Bool)
(declare-const _x3 Bool)
(assert (= true _x0 (= _x3 _x0)))
(assert (and (= true _x0 (= _x3 _x0)) _x0))
(assert (= (and (= true _x0 (= _x3 _x0)) _x0) true _x0))
(check-sat)
