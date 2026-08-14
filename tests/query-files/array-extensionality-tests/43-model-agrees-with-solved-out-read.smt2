; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK: ^sat
; The directives match in the order the model prints, which is j, i, b.
; CHECK-L: (define-fun |j| () (_ BitVec 4) #x0)
; CHECK-L: (define-fun |i| () (_ BitVec 8) #x00)
; CHECK-L: (define-fun |b| () (Array (_ BitVec 4) (_ BitVec 8)) (store ((as const (Array (_ BitVec 4) (_ BitVec 8))) #x00) #x0 #x01))
; Unconstrained-variable elimination reaches this disequality from
; either side: i occurs once, and so does the array b beneath the read.
; The read rule is the one that fires -- select(b,j) with b free is
; itself free -- so the read becomes a fresh value and b is defined as a
; write of it, which is why b prints with an explicit cell rather than
; as the bare constant array. (Before the array rules existed it was i
; that was eliminated, defined from select(b,j), and b printed with no
; cells at all.)
;
; What has to hold, however the elimination goes, is that the model is
; self-consistent: the printed b[j] is the value the evaluation of i
; actually used, so the two disagree exactly as the assertion demands.
; The three values above are pinned together for that reason and only
; that reason -- j selects cell 0, b's cell 0 is #x01, and i is #x00, so
; i /= select(b,j) reading only what was printed. Which particular pair
; of values it is depends on the rewrite order and has changed before;
; if it changes again, check that they still disagree before repinning.
;
; With array equality enabled the model printer emits a *total*
; interpretation for every array, filling in zero wherever it finds no
; concrete-index entry, so a b whose printed cells disagreed with the
; value i was computed from would contradict the assertion the model was
; produced for. The don't-care is zero precisely so that it agrees with
; the completion every other reader of the model applies -- the printer
; here, ReadUsingModel, and the contents comparison the post-solve audit
; makes -- without anything having to be recorded to keep them in step.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun c () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun b () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun i () (_ BitVec 8))
(declare-fun j () (_ BitVec 4))
(assert (not (= a c)))
(assert (not (= i (select b j))))
(check-sat)
(get-model)
