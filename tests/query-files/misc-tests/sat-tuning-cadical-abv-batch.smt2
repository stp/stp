; REQUIRES: cadical, prlimit
; RUN: prlimit --stack=786432 -- %solver --cadical --incremental=off --sat-tuning=auto -s %s 2>&1 | %OutputCheck %s --check-prefix=AUTO
; RUN: prlimit --stack=786432 -- %solver --cadical --incremental=off --sat-tuning=auto --cnf-generation-effort=gia-low -s %s 2>&1 | %OutputCheck %s --check-prefix=EXPLICIT
; AUTO: ^SAT tuning: backend=cadical logic=QF_ABV session=batch profile=cadical-qf-abv-batch$
; AUTO: ^SAT tuning: search-bias=unsat \(automatic\)$
; AUTO: ^SAT tuning: cnf-generation-effort=auto \(automatic\)$
; AUTO: ^SAT tuning: cadical-factor=off \((automatic|explicit)\)$
; AUTO: ^SAT tuning: array-late-read-limit=1024 \(automatic\)$
; AUTO: ^SAT tuning: array-late-expansion-limit=100000 \(automatic\)$
; AUTO: ^SAT tuning: array-late-congruence-limit=16000 \(automatic\)$
; AUTO: ^SAT tuning: array-equality-gia-cnf=true \(automatic\)$
; AUTO: ^SAT tuning: array-equality-gia-min-reads=16 \(automatic\)$
; AUTO: ^sat$
; EXPLICIT: ^SAT tuning: cnf-generation-effort=gia-low \(explicit\)$
; EXPLICIT: ^sat$
;
; Automatic QF_ABV batch tuning must select its bounded array settings before
; the first encoding and preserve an explicit CNF choice.
; This is the mapper-deep-reference-walk reproducer under a logic that selects
; that profile. The 768 KiB stack exercises ABC's explicit-stack reference
; walk. The companion API tests check the settings at the first CNF emission.
; The factoring-off CI sweep explicitly supplies that value, so its diagnostic
; must acknowledge the override even when it matches the automatic default.
(set-logic QF_ABV)
(declare-const t (_ BitVec 255))
(assert (distinct (_ bv0 256) (bvurem ((_ zero_extend 1) t) (bvand (_ bv1 256) ((_ zero_extend 1) t)))))
(check-sat)
