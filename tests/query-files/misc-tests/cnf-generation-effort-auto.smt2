; Choosing the CNF effort from the size of the AIG, end to end: the option, the
; UserFlags fields, and which way the decision goes on either side of the
; threshold.
;
; The query is small -- a handful of AND gates -- so `auto` should leave it on
; medium, where cut enumeration is cheap and the smaller CNF is worth having.
; Moving the threshold down to one gate forces the other branch without needing
; a query large enough to be slow, so this test says nothing about how many
; gates a real query has and does not go stale when the default moves.
;
; RUN: %solver --SMTLIB2 -s %s 2>&1 | %OutputCheck --check-prefix=SMALL %s
; RUN: %solver --SMTLIB2 -s --cnf-generation-effort auto %s 2>&1 | %OutputCheck --check-prefix=SMALL %s
; RUN: %solver --SMTLIB2 -s --cnf-generation-effort auto --cnf-auto-threshold 1 %s 2>&1 | %OutputCheck --check-prefix=BIG %s
;
; SMALL: ^cnf-auto: [0-9]+ AIG nodes, chose medium$
; SMALL: sat
; BIG: ^cnf-auto: [0-9]+ AIG nodes, chose very-low$
; BIG: sat
;
; The fixed levels stay reachable and stay silent: nothing decides anything, so
; there is no line to print.
;
; RUN: %solver --SMTLIB2 -s --cnf-generation-effort medium %s 2>&1 | %OutputCheck --check-prefix=FIXED %s
; RUN: %solver --SMTLIB2 -s --cnf-generation-effort very-low %s 2>&1 | %OutputCheck --check-prefix=FIXED %s
;
; FIXED-NOT: cnf-auto:
; FIXED: sat
;
; And an unknown level is still refused, with auto now among those offered.
;
; RUN: not %solver --SMTLIB2 --cnf-generation-effort nonsense %s 2>&1 | %OutputCheck --check-prefix=BADLEVEL %s
;
; BADLEVEL: Unknown --cnf-generation-effort value 'nonsense'\. Expected one of: auto, very-low, low, medium, high, very-high\.

(set-logic QF_BV)
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
(assert (= (bvand a b) #x0f))
(assert (bvult a b))
(check-sat)
(exit)
