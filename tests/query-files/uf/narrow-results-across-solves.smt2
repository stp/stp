; A narrowed UF result keeps its width out of the name it is looked up by, and
; two solves of the same query must not fight over it.
;
; --uf-narrow-results (on by default) gives a declaration whose results are
; only ever compared to each other a result sort of ceil(log2(N)) bits instead
; of the declared width, where N is how many applications the query has. The
; result symbol is allocated in STP's deterministic namespace, whose whole
; bargain is that the key settles the symbol: one key, one symbol, one sort,
; so an identical block rebuilds an identical root.
;
; N is read off the root being lowered, and the root changes between solves.
; Here f has two applications inside the push and three after the pop, so the
; same durable handle for (f a) wants one bit and then two, under a key that
; was only ever the handle. That tripped the namespace's own guard --
;
;   Fatal Error: a deterministic introduced symbol was requested at two
;   different source sorts
;
; -- which is the guard doing its job: the caller was the one breaking the
; bargain. The width now joins the key, so the two solves allocate two
; symbols instead of disagreeing about one.
;
; Only a narrowed result is tagged that way, so every unnarrowed name is
; untouched -- including the rounding-mode results that a persistent block has
; to rebuild and re-pin by name.
;
; Both drivers, because they reach lowering by different routes and the bug
; needs only a second solve, not a particular way of getting there.
;
; The third leg turns narrowing off, which is the control: with no narrowed
; width there is nothing for the two solves to disagree about, so it says that
; the first two legs are measuring the naming and not the query.
;
; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --uf-narrow-results=0 %s 2>&1 | %OutputCheck %s
;
; CHECK-NOT: Fatal Error
; CHECK-NOT: different source sorts
; CHECK: ^sat$
; CHECK: ^sat$
; CHECK: REACHED-END
;
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
(declare-fun c () (_ BitVec 8))

; Two applications: one bit is enough to tell the results apart.
(push 1)
(assert (= (f a) (f b)))
(check-sat)
(pop 1)

; Three, and now it is not.
(assert (distinct (f a) (f b)))
(assert (distinct (f b) (f c)))
(assert (distinct (f a) (f c)))
(check-sat)
(echo "REACHED-END")
