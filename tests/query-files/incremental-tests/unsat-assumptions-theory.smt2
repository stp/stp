; Theory blocks keep level-based verdict caching conservative, while their
; selectors identify individual user assumptions. A UF conflict must omit p.
; RUN: %solver --incremental --uf-ackermann=off %s | %OutputCheck %s
; RUN: %solver --incremental --uninterpreted-functions %s | %OutputCheck %s
;
(set-option :produce-unsat-assumptions true)
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(declare-fun p () Bool)
(assert (= x y))
(check-sat-assuming ((distinct (f x) (f y)) p))
; CHECK: ^unsat
(get-unsat-assumptions)
; CHECK: ^\(\(distinct .*\)\)$
