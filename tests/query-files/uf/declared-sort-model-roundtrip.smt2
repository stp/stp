; Uninterpreted-sort model values are qualified abstract values, never
; bit-vector carriers. Models contain definitions for the existing signature.
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
; CHECK: ^\(define-fun \|[ab]\| \(\) S \(as \|@S![0-9]+\| S\)\)$
; CHECK: ^\(define-fun \|[ab]\| \(\) S \(as \|@S![0-9]+\| S\)\)$
; CHECK: ^\(define-fun \|f\| \(\(x0 S\)\) S$
; CHECK: \(ite \(= x0 \(as \|@S![0-9]+\| S\)\)
;
; get-value agrees with the model, for a symbol and for an application. That
; agreement is the point: the application's value used to be printed by handing
; the node to the term printer, which produced the carrier.
; CHECK: ^\(a \(as \|@S![0-9]+\| S\)\)$
; CHECK: ^\(\(f a\) \(as \|@S![0-9]+\| S\)\)$
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
