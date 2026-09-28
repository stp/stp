; A model that mentions a declared sort prints at that sort, and reads back.
;
; An element of a sort introduced by declare-sort has no literal. Its carrier
; pattern is not one: printing #x0000 for it names a bit-vector, which is the
; one thing the sort exists to say it is not -- and the model used to do exactly
; that, giving `(define-fun |u| () (_ BitVec 16) #x0000)` for a symbol of sort
; T. SMT-LIB's answer, and every solver's, is to give the elements names and let
; distinct names denote distinct elements, which is also the only part of this
; format that cannot be stated outright.
;
; So the model declares the sorts it mentions, declares one constant per element
; it mentions, and refers to those. That is what makes it re-readable: nothing
; else knows what the elements of S are. The body is rendered before the
; preamble is printed, because rendering it is what names the elements.
;
; get-value goes through a different printer and had to be brought along, twice
; -- once for a symbol and once for an application, whose value was printed by
; handing the node to the term printer and so came back as the carrier. The two
; must agree: a caller that reads a model and then asks for one of its values
; should not be told two different things.
;
; RUN: %solver --uninterpreted-functions --incremental=off -p %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on -p %s 2>&1 | %OutputCheck %s
;
; Which element the solver picks for a symbol, and how many elements it names,
; are its own business -- the two pipelines legitimately differ, since nothing
; in the query pins f's value away from a and b. What is checked is the form:
; every value of sort S is a named element of S, and no carrier width appears
; anywhere in the model.
;
; CHECK: ^sat
; CHECK: ^\(declare-sort S 0\)$
; CHECK: ^\(declare-fun \|S![0-9]+\| \(\) S\)$
; CHECK: ^\(declare-fun \|S![0-9]+\| \(\) S\)$
; CHECK: ^\(define-fun \|[ab]\| \(\) S \|S![0-9]+\|\)$
; CHECK: ^\(define-fun \|[ab]\| \(\) S \|S![0-9]+\|\)$
; CHECK: ^\(define-fun \|f\| \(\(x0 S\)\) S$
; CHECK: \(ite \(= x0 \|S![0-9]+\|\)
;
; get-value agrees with the model, for a symbol and for an application. That
; agreement is the point: the application's value used to be printed by handing
; the node to the term printer, which produced the carrier.
; CHECK: ^\( \|a\| \|S![0-9]+\| \)$
; CHECK: ^\( \(\|f\| \|a\|\) \|S![0-9]+\| \)$
;
; There is deliberately no CHECK-NOT for the carrier width. A negative in this
; tool spans only the gap between the positives around it, so one placed at the
; end covers the text after the last match and nothing before it -- verified by
; injecting a carrier line and watching it pass. The positives do the work
; instead: every symbol in this query is of sort S, so a leaked carrier makes
; the line read `() (_ BitVec 16) #x0000` and fails the define-fun check above.
;
(set-logic QF_UFBV)
(declare-sort S 0)
(declare-fun f (S) S)
(declare-fun a () S)
(declare-fun b () S)
(assert (distinct a b))
(assert (= (f a) b))
(check-sat)
(get-value (a (f a)))
