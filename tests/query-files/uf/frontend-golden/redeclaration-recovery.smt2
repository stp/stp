; Every top-level declaration kind shares one namespace, and only the
; NONZERO-ARITY declare-fun -- the one shape the legacy grammar could not
; parse at all -- adopts report-and-continue over a known name: the
; rejected declaration is command-local, registers nothing, and leaves the
; original binding usable.  Zero-arity redeclarations are UF-free shapes and
; keep the legacy classified-token syntax error and parse abandonment (see
; zero-arity-redeclare-pinned, zero-arity-uf-name-pinned,
; declare-const-known-name-pinned, define-fun-known-name-pinned).
;
; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions %s 2>&1 | %OutputCheck %s
; CHECK-NEXT: ^\(error ".*g.*already.*"\)
; CHECK-NEXT: ^\(error ".*d.*define-fun"\)
; CHECK-NEXT: ^\(error ".*s.*ordinary symbol"\)
; CHECK-NEXT: ^unsat
; CHECK-NEXT: ^"REACHED-END"
; CHECK-NOT: syntax error
;
(set-logic QF_UFBV)
(declare-fun g ((_ BitVec 8)) (_ BitVec 8))
(define-fun d ((x (_ BitVec 8))) (_ BitVec 8) (bvnot x))
(declare-const s (_ BitVec 8))
(declare-fun g ((_ BitVec 8)) (_ BitVec 4))
(declare-fun d ((_ BitVec 8)) (_ BitVec 8))
(declare-fun s ((_ BitVec 8)) (_ BitVec 8))
(assert (distinct (g #x03) (g #x03)))
(check-sat)
(echo "REACHED-END")
