; A CBP adoption may replace an opaque Boolean shell and emit the original
; shell as a pinning fact.  That fact is a real conjunct of the level, so its
; symbols must keep same-level definitions from being eliminated as private.
; The old order prepared only the adopted equality, eliminated `result`, and
; appended the range fact afterwards; its unconstrained `result` made the
; incremental round spuriously satisfiable.  The first round also caches the
; equality with `result` legitimately eliminated, so the third round checks
; that fact protection invalidates that now-unsafe cache entry.  Under default
; engagement the first two rounds use the batch solver and the buggy shape is
; instead the incremental driver's first round.  The fourth round re-pushes
; the identical scope to exercise CBP memo replay.
; RUN: %solver --array-equality --check-sanity %s | %OutputCheck %s
; RUN: %solver --incremental --check-sanity %s | %OutputCheck %s
; RUN: %solver --incremental-auto-engage-at 1 --check-sanity %s | %OutputCheck %s
; RUN: %solver --incremental --incremental-cbp-reset --check-sanity %s | %OutputCheck %s
; RUN: %solver --incremental --incremental-profile --check-sanity %s 2>&1 | %OutputCheck --check-prefix=PROFILE %s
(set-logic QF_FP)
(define-fun f10 () Float32 ((_ to_fp 8 24) #x41200000))
(define-fun f0_4 () Float32 ((_ to_fp 8 24) #x3ecccccd))
(declare-fun result () Float32)
(declare-fun flag () Bool)

(push 1)
(assert (= result (fp.mul RNE f10 f0_4)))
; CHECK-NEXT: ^sat
(check-sat)
(pop 1)

(push 1)
(assert flag)
; CHECK-NEXT: ^sat
(check-sat)
(pop 1)

(push 1)
(assert (= result (fp.mul RNE f10 f0_4)))
(assert (not (and (fp.geq result ((_ to_fp 8 24) #x40599970))
                  (fp.leq result ((_ to_fp 8 24) #x40800015)))))
; CHECK-NEXT: ^unsat
; PROFILE: Incremental profile work: check=3 .*prepare-invalidated=1
; PROFILE: ^unsat
(check-sat)
(pop 1)

(push 1)
(assert (= result (fp.mul RNE f10 f0_4)))
(assert (not (and (fp.geq result ((_ to_fp 8 24) #x40599970))
                  (fp.leq result ((_ to_fp 8 24) #x40800015)))))
; CHECK-NEXT: ^unsat
; PROFILE: Incremental profile work: check=4 .*prepare-hits=1
; PROFILE: Incremental profile cbp/backend: check=4 .*cbp-replay-attempts=1 cbp-replays=1
; PROFILE: ^unsat
(check-sat)
(pop 1)
(exit)
