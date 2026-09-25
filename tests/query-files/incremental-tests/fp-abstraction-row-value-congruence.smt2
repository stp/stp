; A cache-hit re-solve must materialise driver read rows with the row's FULL
; value term -- the congruence if-then-else over previously minted reads --
; never the bare read symbol, which is only the all-indices-distinct branch.
;
; The shape: a symbolic-index read (select A i) rides an if-then-else
; ITE(i = 7, s_7, s_i) in the encoding. The inequalities pin i to 7 without
; giving equality propagation a substitution, so the SAT solver decides the
; branch and s_i's bits stay entirely free. The second check-sat is a
; content-identical re-push: its encoding is a cache hit and model
; construction re-materialises the read rows from the driver's persistent
; pair record. Binding the cell A[7] to free s_i instead of the if-then-else
; publishes a model the raw stack refutes: the third assertion re-derives
; A[7] structurally through a disjoint store and sees the poisoned cell.
; The self-check (-d) then aborts, though every answer is correct.
;
; The wrong binding fires only when the map order interleaves the rows
; unfavourably, so this test pins the fixed behaviour (both checks sat and
; the self-check silent) rather than a specific failure message.
;
; RUN: %solver --incremental=on --fp-abstraction=true --fp-abstraction-incremental=true -d %s 2>&1 | %OutputCheck %s
; CHECK: ^sat$
; CHECK: ^sat$
(set-logic QF_ABVFP)
(declare-fun A () (Array (_ BitVec 32) (_ BitVec 32)))
(declare-fun i () (_ BitVec 32))
(declare-fun f () (_ FloatingPoint 8 24))
(push 1)
(assert (fp.isNormal f))
(assert (bvule i #x00000007))
(assert (bvuge i #x00000007))
(assert (= (select A i) #x00000001))
(assert (= (select A #x00000007) #x00000001))
(assert (= (select (store A #x00000008 #x00000003) #x00000007) #x00000001))
(check-sat)
(pop 1)
(push 1)
(assert (fp.isNormal f))
(assert (bvule i #x00000007))
(assert (bvuge i #x00000007))
(assert (= (select A i) #x00000001))
(assert (= (select A #x00000007) #x00000001))
(assert (= (select (store A #x00000008 #x00000003) #x00000007) #x00000001))
(check-sat)
(pop 1)
(exit)
