; Choosing the CNF effort from the size of the AIG, end to end: the option, the
; UserFlags fields, and which way the decision goes on either side of the
; threshold.
;
; The query is small -- a handful of AND gates -- so `auto` resolves it to
; gia-low from the recorded estimate. Moving the threshold down to one gate
; forces the new-medium branch without needing a query large enough to be
; slow, so this test says nothing about how many gates a real query has and
; does not go stale when the default moves.
;
; The estimate-based resolution requires the CaDiCaL backend; other backends
; keep the older size-based choice, which the array-fallback test covers.
; Compiled in -- what the gate below checks -- is not default: CryptoMiniSat
; is the default wherever it is installed, so the auto runs say --cadical.
; REQUIRES: cadical
;
; RUN: %solver --SMTLIB2 -s --cadical %s 2>&1 | %OutputCheck --check-prefix=SMALL %s
; RUN: %solver --SMTLIB2 -s --cadical --cnf-generation-effort auto %s 2>&1 | %OutputCheck --check-prefix=SMALL %s
; RUN: %solver --SMTLIB2 -s --cadical --cnf-generation-effort auto --cnf-auto-threshold 1 %s 2>&1 | %OutputCheck --check-prefix=BIG %s
;
; SMALL: ^cnf-auto: estimated [0-9]+ AND nodes, chose gia-low$
; SMALL: ^gia: [0-9]+ AND nodes, [0-9]+ inputs, LUT3$
; SMALL: ^cnf: [0-9]+ clauses, [0-9]+ variables, [0-9]+ literals$
; SMALL: ^sat$
; BIG: ^cnf-auto: estimated [0-9]+ AND nodes, chose new-medium$
; BIG: ^new-medium CNF$
; BIG: ^sat$
;
; The fixed levels stay reachable and stay silent: nothing decides anything, so
; there is no line to print.
;
; RUN: %solver --SMTLIB2 -s --cnf-generation-effort medium %s 2>&1 | %OutputCheck --check-prefix=FIXED %s
; RUN: %solver --SMTLIB2 -s --cnf-generation-effort very-low %s 2>&1 | %OutputCheck --check-prefix=FIXED %s
;
; FIXED-NOT: cnf-auto:
; FIXED: ^sat$
;
; And an unknown level is still refused, with auto now among those offered.
;
; RUN: not %solver --SMTLIB2 --cnf-generation-effort nonsense %s 2>&1 | %OutputCheck --check-prefix=BADLEVEL %s
;
; BADLEVEL: Unknown --cnf-generation-effort value 'nonsense'\. Expected one of: auto, very-low, low, medium, high, very-high, new-very-low, new-low, new-medium, gia-low, gia-high, gia-very-high\.
;
; The new-* rungs are a different generator over a different AIG, so they
; say so rather than printing one of the ABC lines.
;
; RUN: %solver --SMTLIB2 -s --cnf-generation-effort new-very-low %s 2>&1 | %OutputCheck --check-prefix=NEWVERYLOW %s
; RUN: %solver --SMTLIB2 -s --cnf-generation-effort new-low %s 2>&1 | %OutputCheck --check-prefix=NEWLOW %s
; RUN: %solver --SMTLIB2 -s --cnf-generation-effort new-medium %s 2>&1 | %OutputCheck --check-prefix=NEWMEDIUM %s
;
; NEWVERYLOW-NOT: cnf-auto:
; NEWVERYLOW-NOT: advanced CNF
; NEWVERYLOW: ^new-very-low CNF$
; NEWVERYLOW: ^sat$
;
; NEWLOW: ^new-low CNF$
; NEWLOW: ^sat$
;
; NEWMEDIUM: ^new-medium CNF$
; NEWMEDIUM: ^sat$
;
; The gia-* rungs reach Mf_ManGenerateCnf, the same generator low, high and
; very-high reach, over a Gia the blaster built rather than one converted from
; an ABC AIG. They print the graph they hand over -- which is how a reader
; tells the two backends apart at the same LUT size -- and auto never picks
; one, for the same reason it never picks the rungs above.
;
; RUN: %solver --SMTLIB2 -s --cnf-generation-effort gia-low %s 2>&1 | %OutputCheck --check-prefix=GIALOW %s
; RUN: %solver --SMTLIB2 -s --cnf-generation-effort gia-high %s 2>&1 | %OutputCheck --check-prefix=GIAHIGH %s
; RUN: %solver --SMTLIB2 -s --cnf-generation-effort gia-very-high %s 2>&1 | %OutputCheck --check-prefix=GIAVHIGH %s
;
; GIALOW-NOT: cnf-auto:
; GIALOW-NOT: Nodes before AIG rewrite:
; GIALOW: ^gia: [0-9]+ AND nodes, [0-9]+ inputs, LUT3$
; GIALOW: ^cnf: [0-9]+ clauses, [0-9]+ variables, [0-9]+ literals$
; GIALOW: ^sat$
;
; GIAHIGH: ^gia: [0-9]+ AND nodes, [0-9]+ inputs, LUT6$
; GIAHIGH: ^sat$
;
; GIAVHIGH: ^gia: [0-9]+ AND nodes, [0-9]+ inputs, LUT8$
; GIAVHIGH: ^sat$

(set-logic QF_BV)
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
(assert (= (bvand a b) #x0f))
(assert (bvult a b))
(check-sat)
(exit)
