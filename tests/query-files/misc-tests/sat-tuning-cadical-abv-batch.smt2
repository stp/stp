; REQUIRES: cadical, prlimit
; RUN: prlimit --stack=786432 -- %solver --cadical --incremental=off --sat-tuning=auto -s %s 2>&1 | %OutputCheck %s
; CHECK: ^SAT tuning: backend=cadical logic=QF_ABV session=batch profile=cadical-qf-abv-batch$
; CHECK: ^SAT tuning: search-bias=unsat \(automatic\)$
; CHECK: ^SAT tuning: cnf-generation-effort=gia-low \(automatic\)$
; CHECK: ^SAT tuning: cadical-factor=off \(automatic\)$
; CHECK: ^sat$
;
; Automatic QF_ABV batch tuning must select gia-low before the first encoding.
; This is the mapper-deep-reference-walk reproducer under a logic that selects
; that profile. The 768 KiB stack exercises ABC's explicit-stack reference
; walk. The companion API tests check the settings at the first CNF emission.
(set-logic QF_ABV)
(declare-const t (_ BitVec 255))
(assert (distinct (_ bv0 256) (bvurem ((_ zero_extend 1) t) (bvand (_ bv1 256) ((_ zero_extend 1) t)))))
(check-sat)
