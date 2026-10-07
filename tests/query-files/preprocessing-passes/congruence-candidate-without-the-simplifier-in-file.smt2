; The same abort reached from inside the file rather than from the command
; line. Both options are `settable` in the registry, so a file may turn the
; simplifier off and the pass on with nothing on the command line at all --
; which is how this was found.
;
; Worth its own file because the two routes write the flag through different
; code: the command line resolves exclusions before the solver starts, and
; set-option writes the registry while it is running.
; RUN: %solver -s %s 2>&1 | %OutputCheck %s
; CHECK: proposed:2 tested:2 proved:1
; CHECK: ^unsat$
(set-option :disable-opt-inc true)
(set-option :congruence-candidates true)
(set-logic QF_BV)
(declare-fun a () (_ BitVec 16))
(declare-fun b () (_ BitVec 16))
(declare-fun d () (_ BitVec 16))
(assert
  (not (=
    (bvudiv (bvadd (bvmul (_ bv3 16) a) (bvsub b a)) d)
    (bvudiv (bvadd (bvadd a a) (bvadd b (_ bv0 16))) d))))
(check-sat)
(exit)
