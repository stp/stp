; The three ways a printed model failed to read back, each in a block.
;
; The previous fixture checked the model's shape with regexes and stopped, so
; every one of these shipped green under a commit whose message asserted that
; the model "parses and answers sat". Nothing in the tree fed solver output
; back to the solver, which is the only check that would have caught them.
; This file cannot do that either -- lit has no way to pipe one run's output
; into the next -- so it pins the three properties that make a replay possible,
; each chosen because its absence was a real failure:
;
;   1. a sort reaching the model through a signature ALONE is still declared.
;      A predicate over an opaque sort names no element, so building the
;      preamble from named elements omitted its (declare-sort) entirely and the
;      replay died at the first use of the name. This is the commonest QF_UF
;      shape there is.
;   2. a sort name that is not a simple symbol is quoted. (declare-sort
;      |my sort| 0) is legal and printed bare, so the model was a syntax error.
;   3. an element name the query itself declared is stepped over. The model
;      declares its element constants, so inventing |S!0| when the input
;      already has one produced a model that declared it twice.
;
; RUN: %solver --uninterpreted-functions --incremental=off -p %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on -p %s 2>&1 | %OutputCheck %s
;
; A sort used only as a domain, with no constant of it anywhere.
; CHECK: ^sat
; CHECK: ^\(declare-sort S 0\)$
; CHECK: ^\(define-fun \|h\| \(\(x0 S\)\) Bool$
; CHECK: SIGNATURE-ONLY-DONE
;
; A sort name needing quotes, in the declaration, the element and the value.
; CHECK: ^\(declare-sort \|my sort\| 0\)$
; CHECK: ^\(declare-fun \|my sort![0-9]+\| \(\) \|my sort\|\)$
; CHECK: ^\(define-fun \|[ab]\| \(\) \|my sort\| \|my sort![0-9]+\|\)$
; CHECK: QUOTED-DONE
;
; The query owns S!0, so the model's own elements start past it and the two
; never collide.
; CHECK: ^\(declare-sort S 0\)$
; CHECK-NOT: ^\(declare-fun \|S!0\| \(\) S\)$
; CHECK: ^\(define-fun \|S!0\| \(\) S \|S![1-9][0-9]*\|\)$
;
(set-logic QF_UFBV)
(declare-sort S 0)
(declare-fun h (S) Bool)
(declare-fun z () (_ BitVec 4))
(assert (= z #x1))
(check-sat)
(get-model)
(echo "SIGNATURE-ONLY-DONE")
(reset)
(set-logic QF_UFBV)
(declare-sort |my sort| 0)
(declare-fun a () |my sort|)
(declare-fun b () |my sort|)
(assert (distinct a b))
(check-sat)
(get-model)
(echo "QUOTED-DONE")
(reset)
(set-logic QF_UFBV)
(declare-sort S 0)
(declare-fun |S!0| () S)
(declare-fun b () S)
(assert (distinct |S!0| b))
(check-sat)
(get-model)
