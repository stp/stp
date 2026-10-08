; RUN: %solver %s | %OutputCheck %s
;
; A float-tier reroute abandons a solve that may already have stated
; congruence lemmas in place. Those lemmas lived only in the abandoned solve,
; but the lazy rounds still counted them as stated. So the re-solve on the
; exact driver -- a new solve over the query and only the lemmas the restart
; loop had found itself -- met the same pairs broken, dropped them as already
; known, and answered sat on a model giving two congruent applications of f
; different values. Publishing that model then failed STP's own audit: "sat",
; followed by "UF model: congruent applications have different values" and a
; poisoned term manager. A new solve now starts from every lemma stated so
; far, in place or not.
;
; Reduced from stp/stp#1282. The floor of 0 is what lets the reroute fire on a
; tableau this small. This file is a witness, not a robust trigger: the solve
; only states lemmas in place before its fill crosses the reroute budget with
; CaDiCaL as the backend and the decision-polarity advice that STP's patched
; copy of it provides. The lra-* sweep runs this file under --cadical, which
; is the run that covers it wherever CryptoMiniSat is the default.
;
; CHECK: ^sat$
; CHECK: ^\(define-fun \|f\| \(\(x0 Real\)\) Real$
; CHECK: ^\(define-fun \|p\| \(\(x0 Real\)\) Bool$
(set-option :produce-models true)
(set-option :lra-float-reroute-floor 0)
(declare-const c Bool)
(declare-const y Real)
(declare-const x Real)
(declare-const z Real)
(declare-fun f (Real) Real)
(declare-fun p (Real) Bool)
(declare-const v Real)
(assert (and (p z) (or c (= (p 0.0) (p (ite (p 0.0) z 0.0)))) (p y)))
(assert (distinct (p (ite (p (f (+ v (f v)))) 1 0)) (or (distinct 0.0 (+ x (f 0.0))) (and (not (p (ite (p (ite (p (f 0.0)) 1 0)) (+ (f x) (f (+ v (f v)))) 0))) (distinct (f z) (ite (> z 0) 0.0 (f (+ z (f v)))))))))
(assert (or c (p (ite (p 0.0) 1.0 0.0))))
(check-sat)
(get-model)
