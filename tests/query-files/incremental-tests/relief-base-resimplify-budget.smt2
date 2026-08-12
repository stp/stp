; A relief rebuild re-derives the whole base semantically before re-encoding
; it: equality propagation, substitution, and constant-bit propagation over
; every base conjunct at once. That pass had no budget of its own, and the
; rebuild it belongs to has none either. e093b0d2 took it off the three
; rebuild reasons that are pure SAT reconfiguration; on relief -- the one
; reason that IS about size -- it stayed unbounded, measured at 9.4 s on a
; 23,294-conjunct base inside a single rebuild.
;
; It is an optimisation, so a base too large to digest can simply be
; re-encoded raw: that is already what an array base does, and what the
; other three rebuild reasons now do. The budget makes the size the trigger.
;
; This session takes relief rebuilds by design (a small permanent base, a
; pushed level per round that is popped and never revisited, and a low
; re-encode limit). With the budget below the base's size the pass is
; skipped; the answers must not move -- against the unbudgeted pass, and
; against the batch pipeline, both checked here.
; RUN: %solver --incremental -s --incremental-reencode-limit 500 --incremental-base-resimplify-limit 10 %s 2>&1 | %OutputCheck %s
; RUN: %solver --incremental-auto-engage-at 1 -s --incremental-reencode-limit 500 --incremental-base-resimplify-limit 10 %s 2>&1 | %OutputCheck %s
; RUN: %solver --incremental --incremental-reencode-limit 500 --incremental-base-resimplify-limit 10 --check-sanity %s | %OutputCheck --check-prefix=ANSWERS %s
; RUN: %solver --incremental --incremental-reencode-limit 500 --check-sanity %s | %OutputCheck --check-prefix=ANSWERS %s
; RUN: %solver --check-sanity %s | %OutputCheck --check-prefix=ANSWERS %s
;
; the rebuild happens, and skips the pass rather than paying it unbounded
; CHECK: base re-simplification skipped \(base over 10 nodes\)
; CHECK-NOT: base re-simplified at rebuild
(set-logic QF_BV)
(declare-fun b0 () (_ BitVec 16))
(declare-fun b1 () (_ BitVec 16))
(declare-fun b2 () (_ BitVec 16))
(declare-fun b3 () (_ BitVec 16))
(declare-fun b4 () (_ BitVec 16))
(declare-fun b5 () (_ BitVec 16))
(declare-fun b6 () (_ BitVec 16))
(declare-fun b7 () (_ BitVec 16))
(assert (bvult b0 #x7000))
(assert (bvult b1 #x7001))
(assert (bvult b2 #x7002))
(assert (bvult b3 #x7003))
(push 1)
(assert (bvugt (bvmul b0 b0) #x0000))
(assert (bvugt (bvmul b1 b1) #x0001))
(assert (bvugt (bvmul b2 b2) #x0002))
(assert (bvugt (bvmul b3 b3) #x0003))
; ANSWERS: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul b0 b1) #x0007))
(assert (bvugt (bvmul b1 b2) #x0008))
(assert (bvugt (bvmul b2 b3) #x0009))
(assert (bvugt (bvmul b3 b4) #x000a))
; ANSWERS: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul b0 b2) #x000e))
(assert (bvugt (bvmul b1 b3) #x000f))
(assert (bvugt (bvmul b2 b4) #x0010))
(assert (bvugt (bvmul b3 b5) #x0011))
; ANSWERS: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul b0 b3) #x0015))
(assert (bvugt (bvmul b1 b4) #x0016))
(assert (bvugt (bvmul b2 b5) #x0017))
(assert (bvugt (bvmul b3 b6) #x0018))
; ANSWERS: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul b0 b4) #x001c))
(assert (bvugt (bvmul b1 b5) #x001d))
(assert (bvugt (bvmul b2 b6) #x001e))
(assert (bvugt (bvmul b3 b7) #x001f))
; ANSWERS: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul b0 b5) #x0023))
(assert (bvugt (bvmul b1 b6) #x0024))
(assert (bvugt (bvmul b2 b7) #x0025))
(assert (bvugt (bvmul b3 b0) #x0026))
; ANSWERS: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul b0 b6) #x002a))
(assert (bvugt (bvmul b1 b7) #x002b))
(assert (bvugt (bvmul b2 b0) #x002c))
(assert (bvugt (bvmul b3 b1) #x002d))
; ANSWERS: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul b0 b7) #x0031))
(assert (bvugt (bvmul b1 b0) #x0032))
(assert (bvugt (bvmul b2 b1) #x0033))
(assert (bvugt (bvmul b3 b2) #x0034))
; ANSWERS: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul b0 b0) #x0038))
(assert (bvugt (bvmul b1 b1) #x0039))
(assert (bvugt (bvmul b2 b2) #x003a))
(assert (bvugt (bvmul b3 b3) #x003b))
; ANSWERS: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul b0 b1) #x003f))
(assert (bvugt (bvmul b1 b2) #x0040))
(assert (bvugt (bvmul b2 b3) #x0041))
(assert (bvugt (bvmul b3 b4) #x0042))
; ANSWERS: ^sat
(check-sat)
(pop 1)
(exit)
