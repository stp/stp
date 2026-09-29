; The ordered completed root is an internal assumption with no source-level
; conjunct of its own. An unsat result must therefore use the exact-stack
; route's coarse accounting: reporting every check-sat-assuming term is safe,
; while asking the backend for failed literals and silently dropping the
; internal root could produce an invalidly small core. The irrelevant p pins
; that conservative result.
;
; RUN: %solver -s --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: Ordered 1 symmetric distinct group\(s\) in an assumption-scoped incremental block
; CHECK: ^unsat
; CHECK: ^\(.*\|p\|.*\)$
;
(set-logic QF_BV)
(set-option :produce-unsat-assumptions true)
(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
(declare-const c (_ BitVec 8))
(declare-const x (_ BitVec 8))
(declare-const p Bool)
(assert (distinct a b c))
(assert (= x #x00))
(check-sat-assuming ((= x #x01) p))
(get-unsat-assumptions)
