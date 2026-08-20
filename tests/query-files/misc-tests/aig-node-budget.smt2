; The AIG node budget, end to end: option registration, the UserFlags field,
; the cap itself and the verdict an exhausted cap produces.
;
; The query factorises a prime, so there is nothing to simplify away and the
; whole product reaches the bit-blaster: a and b each occur twice, so
; unconstrained-variable elimination cannot collapse the multiply, and the
; ordering constraint keeps the trivial 1 * n factorisation out. Uncapped it
; is a few thousand AND gates and answers sat; capped at a thousand it is
; abandoned. The flip is orders of magnitude away from the boundary in either
; direction, so nothing here depends on the exact gate count.
;
; RUN: %solver --SMTLIB2 %s | %OutputCheck --check-prefix=UNCAPPED %s
; RUN: %solver --SMTLIB2 --aig-node-budget -1 %s | %OutputCheck --check-prefix=UNCAPPED %s
; RUN: %solver --SMTLIB2 --aig-node-budget 100000 %s | %OutputCheck --check-prefix=UNCAPPED %s
;
; An exhausted budget leaves through the soft-timeout path, so the answer is
; the one --max-time gives -- and, like a timeout, exit status 0. -1 is no
; limit and 0 is no gates at all, the same convention --max-num-confl and
; --max-time already use; the two sentinels must not be confusable.
; RUN: %solver --SMTLIB2 --aig-node-budget 1000 %s | %OutputCheck --check-prefix=CAPPED %s
; RUN: %solver --SMTLIB2 --aig-node-budget 0 %s | %OutputCheck --check-prefix=CAPPED %s
;
; Anything below -1, or above the int the AND-gate counter is kept in, would
; be a cap that never fires. Both are refused rather than silently ignored.
; RUN: not %solver --SMTLIB2 --aig-node-budget -2 %s 2>&1 | %OutputCheck --check-prefix=TOOSMALL %s
; RUN: not %solver --SMTLIB2 --aig-node-budget 2147483648 %s 2>&1 | %OutputCheck --check-prefix=TOOBIG %s
;
; The count reached is reported under -s only; nothing else exposes it. The
; quiet run is checked against the merged streams and anchored on the verdict
; so the CHECK-NOTs have output to be false about -- an empty stream would
; satisfy them vacuously.
; RUN: %solver --SMTLIB2 -s --aig-node-budget 1000 %s 2>&1 >/dev/null | %OutputCheck --check-prefix=STATS %s
; RUN: %solver --SMTLIB2 --aig-node-budget 1000 %s 2>&1 | %OutputCheck --check-prefix=QUIET %s
;
; The incremental driver's AIG is persistent, so it is not capped. That is a
; real hole and the warning is what keeps it from being a silent one. The
; no-budget run is anchored the same way, on a line -s always prints.
; RUN: %solver --SMTLIB2 --incremental=on --aig-node-budget 1000 %s 2>/dev/null | %OutputCheck --check-prefix=UNCAPPED %s
; RUN: %solver --SMTLIB2 --incremental=on --aig-node-budget 1000 %s 2>&1 >/dev/null | %OutputCheck --check-prefix=INCWARN %s
; RUN: %solver --SMTLIB2 -s --incremental=on %s 2>&1 >/dev/null | %OutputCheck --check-prefix=NOINCWARN %s
;
; UNCAPPED: ^sat$
; CAPPED: ^Timed Out\.$
; TOOSMALL: ^ERROR: --aig-node-budget must be -1 \(no limit\) or greater$
; TOOBIG: ^ERROR: --aig-node-budget must be at most 2147483647
; STATS: AIG node budget exhausted at [0-9]+ nodes
; QUIET-NOT: AIG node budget exhausted
; QUIET: ^Timed Out\.$
; QUIET-NOT: AIG node budget exhausted
; INCWARN: --aig-node-budget is not enforced on the incremental encoder
; NOINCWARN-NOT: aig-node-budget
; NOINCWARN: Incremental: encoded
; NOINCWARN-NOT: aig-node-budget
(set-logic QF_BV)
(declare-const a (_ BitVec 64))
(declare-const b (_ BitVec 64))
(assert (= (bvmul a b) (_ bv1000003 64)))
(assert (bvult (_ bv1 64) a))
(assert (bvult a b))
(check-sat)
