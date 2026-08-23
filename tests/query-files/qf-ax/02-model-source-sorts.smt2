; Models expose the source sorts on array declarations, constants, stores and
; values. The internal 16-bit carrier must not leak out as an array component
; or as a literal pretending to be an Index/Element value.
;
; RUN: %solver --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --incremental=on  %s 2>&1 | %OutputCheck %s
; CHECK: ^sat
; CHECK: ^\(declare-sort Element 0\)$
; CHECK: ^\(declare-sort Index 0\)$
; CHECK: ^\(declare-fun \|Element![0-9]+\| \(\) Element\)$
; CHECK: ^\(declare-fun \|Index![0-9]+\| \(\) Index\)$
; CHECK: ^\(define-fun \|a\| \(\) \(Array Index Element\) \(store \(\(as const \(Array Index Element\)\) \|Element![0-9]+\|\) \|Index![0-9]+\| \|Element![0-9]+\|\)\)$
; CHECK: ^\( \(select \|a\| \|i\|\) \|Element![0-9]+\| \)$
;
(set-logic QF_AX)
(set-option :produce-models true)
(declare-sort Index 0)
(declare-sort Element 0)
(declare-fun a () (Array Index Element))
(declare-fun b () (Array Index Element))
(declare-fun i () Index)
(declare-fun e () Element)
(assert (= (select a i) e))
(assert (not (= a b)))
(check-sat)
(get-model)
(get-value ((select a i)))
