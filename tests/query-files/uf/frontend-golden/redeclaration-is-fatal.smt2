; Every top-level declaration kind shares one namespace, and a nonzero-arity
; declare-fun over a name any of them already owns is refused. That shape --
; the one the legacy grammar could not parse at all -- used to report and
; continue, leaving the original binding usable; it now ends the session like
; every other rejection here. Zero-arity redeclarations were always fatal and
; keep the legacy classified-token syntax error and parse abandonment (see
; zero-arity-redeclare-pinned, zero-arity-uf-name-pinned,
; declare-const-known-name-pinned, define-fun-known-name-pinned).
;
; RUN: not %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: not %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; RUN: not %solver --uninterpreted-functions %S/Inputs/redeclare-over-define-fun.smt2 2>&1 | %OutputCheck --check-prefix=OVERDEF %s
; RUN: not %solver --uninterpreted-functions %S/Inputs/redeclare-over-scalar.smt2 2>&1 | %OutputCheck --check-prefix=OVERSCALAR %s
;
; CHECK-NEXT: ^\(error ".*g.*already.*"\)
; CHECK-NOT: ^unsat
; CHECK-NOT: ^"REACHED-END"
; CHECK-NOT: syntax error
;
; OVERDEF: ^\(error ".*d.*define-fun"\)
; OVERDEF-NOT: ^"REACHED-END"
; OVERDEF-NOT: syntax error
;
; OVERSCALAR: ^\(error ".*s.*ordinary symbol"\)
; OVERSCALAR-NOT: ^"REACHED-END"
; OVERSCALAR-NOT: syntax error
;
; One owner per input: the first collision ends the run, so the three cannot
; share a file any more.
(set-logic QF_UFBV)
(declare-fun g ((_ BitVec 8)) (_ BitVec 8))
(declare-fun g ((_ BitVec 8)) (_ BitVec 4))
(assert (distinct (g #x03) (g #x03)))
(check-sat)
(echo "REACHED-END")
