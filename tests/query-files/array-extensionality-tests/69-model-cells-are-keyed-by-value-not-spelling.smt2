; RUN: %solver -d --array-equality %s | %OutputCheck %s
; CHECK: ^sat
; A rounding-mode or float constant interns apart from the plain
; bit-vector constant with its bits, so one array cell can be recorded
; in the model under two index nodes that denote one index. The entry
; collector keyed its per-index map on the node, so that one cell became
; two entries and the printer emitted it as two stores of the same value
; to the same index -- a model that replays correctly, since the stores
; are idempotent, but that says a cell twice and does not match what
; cvc5 or bitwuzla print for the same query.
;
; Both arrays here have two cells and must therefore print exactly two
; stores each. The RoundingMode-indexed one is the case that showed the
; duplication; the float-indexed one is the same defect in the other
; sort whose constants intern apart. An array indexed by plain
; bit-vectors was never affected, whatever its element sort, because the
; key is the index.
; CHECK-L: (define-fun |floats| () (Array (_ FloatingPoint 5 11) (_ BitVec 4)) (store (store ((as const (Array (_ FloatingPoint 5 11) (_ BitVec 4))) #x0) (fp #b0 #b01111 #b1000000000) #xA) (fp #b0 #b10000 #b0100000000) #x3))
; CHECK-L: (define-fun |modes| () (Array RoundingMode (_ BitVec 4)) (store (store ((as const (Array RoundingMode (_ BitVec 4))) #x0) RTP #x9) RNA #x6))
(set-logic QF_ABVFP)
(declare-const modes (Array RoundingMode (_ BitVec 4)))
(declare-const floats (Array (_ FloatingPoint 5 11) (_ BitVec 4)))
(assert (= (select modes RTP) #b1001))
(assert (= (select modes RNA) #b0110))
(assert (= (select floats (fp #b0 #b01111 #b1000000000)) #b1010))
(assert (= (select floats (fp #b0 #b10000 #b0100000000)) #b0011))
(check-sat)
(get-model)
