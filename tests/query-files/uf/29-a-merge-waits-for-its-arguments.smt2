; Under a = 2 the query equates (f a) with (f 2), and the pre-lowering pass
; reads both facts in one round. Two equated applications merge, the later
; to the earlier, so (f 2) would be sent to (f a); but the round also sends
; a to 2, and rewriting (f a) rebuilds (f 2). That merge sent the rewrite
; round in circles, and STP grew without bound and never answered, in
; every --incremental mode. A merge whose surviving application has an
; argument the round rewrites now waits for the next round, which reads
; (f 2) = (f 2): no merge, and no application left.
;
; RUN: %solver -s --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver -s --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: UF: pre-lowering substituted 1 symbol\(s\) and 0 application\(s\) and 0 asserted atom\(s\) in 1 round\(s\), 0 application\(s\) remain
; CHECK: ^sat$
;
; EXPECT: sat
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 4)) (_ BitVec 4))
(declare-const a (_ BitVec 4))
(assert (= a #x2))
(assert (= (f a) (f #x2)))
(check-sat)
