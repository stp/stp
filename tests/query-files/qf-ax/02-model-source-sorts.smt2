; Models expose the source sorts on array declarations, constants, stores and
; values. The internal 16-bit carrier must not leak out as an array component
; or as a literal pretending to be an Index/Element value.
;
; RUN: %solver --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --incremental=on  %s 2>&1 | %OutputCheck %s
; CHECK: ^sat
; CHECK: ^\(define-fun \|a\| \(\) \(Array Index Element\) \(store \(\(as const \(Array Index Element\)\) \(as \|@Element![0-9]+\| Element\)\) \(as \|@Index![0-9]+\| Index\) \(as \|@Element![0-9]+\| Element\)\)\)$
; CHECK: ^\(\(select a i\) \(as \|@Element![0-9]+\| Element\)\)$
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
