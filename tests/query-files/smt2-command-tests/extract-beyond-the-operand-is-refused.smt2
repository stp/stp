; RUN: not %solver %s 2>&1 | %OutputCheck %s
; An extract reaching past its operand ends the parse. The grammar used to
; report it and build the extract anyway; over a constant the factory then
; folded it, reading past the constant's bits.
(set-logic QF_BV)
(assert (= ((_ extract 9 0) #x00) #b0000000000))
(check-sat)
; CHECK-L: Parsing: Wrong width in BVEXTRACT
; CHECK-NOT: BVTypeCheck
; CHECK-NOT: sat
