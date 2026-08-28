; The sorts a UF signature may name, pinned from both sides. An unsupported
; one is refused at the declaration; RoundingMode and FloatingPoint are on the
; admitted side and are exercised as such, so a regression that re-rejected
; either would fail here as loudly as one that admitted Array.
;
; RUN: not %solver --uninterpreted-functions %s 2>&1 | %OutputCheck %s
; RUN: not %solver --uninterpreted-functions %S/Inputs/uf-sort-reject-domain-unknown.smt2 2>&1 | %OutputCheck --check-prefix=UNKNOWN %s
; RUN: not %solver --uninterpreted-functions %S/Inputs/uf-sort-reject-domain-zero-width.smt2 2>&1 | %OutputCheck --check-prefix=ZEROWIDTH %s
; RUN: not %solver --uninterpreted-functions %S/Inputs/uf-sort-reject-result-array.smt2 2>&1 | %OutputCheck --check-prefix=RESULT %s
; RUN: %solver --uninterpreted-functions %S/Inputs/uf-sort-admitted.smt2 | %OutputCheck --check-prefix=ADMITTED %s
;
; CHECK: unsupported domain sort \(Array \(_ BitVec 8\) \(_ BitVec 8\)\) at argument 0 of bad-array
; CHECK-NOT: ^sat
;
; UNKNOWN: unsupported domain sort UnknownSort at argument 0 of bad-unknown \(unknown
; UNKNOWN-NOT: ^sat
;
; ZEROWIDTH: unsupported domain sort \(_ BitVec 0\) at argument 0 of bad-zero
; ZEROWIDTH-NOT: ^sat
;
; RESULT: unsupported result sort \(Array \(_ BitVec 8\) \(_ BitVec 8\)\) of bad-result
; RESULT-NOT: ^sat
;
; ADMITTED: ^sat
; ADMITTED-NOT: unsupported domain sort
; ADMITTED-NOT: unsupported result sort
;
; One rejection per input: a refused declaration ends the run, so the four
; cannot share a file.
(set-logic QF_UFABVFP)
(declare-fun bad-array ((Array (_ BitVec 8) (_ BitVec 8))) Bool)
(check-sat)
