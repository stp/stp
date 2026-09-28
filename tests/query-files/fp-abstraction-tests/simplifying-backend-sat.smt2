; REQUIRES: minisat
; RUN: %solver -d --fp-abstraction=1 --cnf-generation-effort=new-medium --simplifying-minisat %s | %OutputCheck %s
; CHECK: ^sat
; The floating-point abstraction on a SAT backend that eliminates
; variables. Its lemmas are spliced onto the proxies' and surrogates'
; variables in later solve calls, and nothing froze them: a lemma over an
; eliminated variable aborted in SimpSolver::addClause_ on
; `!isEliminated(var(ps[i]))', or, with MiniSat's assertions off, left a
; candidate the FP check accepted and the original formula refuted, and
; the driver stopped with "refinement reached undecided without a pending
; candidate-blocking lemma".
(set-logic QF_FP)
(declare-const x Float64)
(declare-fun v () Float32)
(declare-fun r () RoundingMode)
(assert (distinct true (distinct (fp.gt (fp.mul r (fp (_ bv1 1) (_ bv0 11) (_ bv1 52)) (fp (_ bv1 1) (_ bv0 11) (_ bv1 52))) (fp (_ bv0 1) (_ bv0 11) (_ bv0 52))) (not (fp.leq (fp.div RNA v ((_ to_fp 8 24) RTP x)) (fp (_ bv0 1) (_ bv0 8) (_ bv0 23)))))))
(check-sat)
