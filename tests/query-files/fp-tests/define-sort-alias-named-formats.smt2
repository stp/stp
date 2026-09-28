; RUN: %solver %s | %OutputCheck %s
;
; define-sort reaches the named IEEE sorts as raw text -- SKIP_SEXPR swallows
; its body and the grammar re-tokenises it by hand -- so it cannot share a
; code path with the sort rule, only the width table (namedFloatFormat).
;
; Nothing exercised the alias route for a named format: both other define-sort
; tests spell the sort as (_ FloatingPoint eb sb). That matters because these
; widths have been wrong before -- the named sorts once split the packed total
; in two (4+12, 16+48, 32+96) rather than use the IEEE fields, so every one but
; Float32 named a format that does not exist. Float32 is deliberately not among
; the cases below: 8+24 is the one split that happens to come out right.
;
; Each alias is pinned by requiring it to agree with the spelled-out format:
; fp.eq rejects operands of different formats outright, so a wrong table is an
; error rather than a different answer. Checking sorts this way rather than
; reading them out of (get-model) keeps the test independent of the order the
; model printer happens to emit its symbols in.
; CHECK: ^sat
(set-logic QF_FP)
(define-sort Half () Float16)
(define-sort Double () Float64)
(define-sort Quad () Float128)
(declare-const h Half)
(declare-const d Double)
(declare-const q Quad)
(declare-const h_spelled (_ FloatingPoint 5 11))
(declare-const d_spelled (_ FloatingPoint 11 53))
(declare-const q_spelled (_ FloatingPoint 15 113))
(assert (fp.eq h h_spelled))
(assert (fp.eq d d_spelled))
(assert (fp.eq q q_spelled))
(check-sat)
