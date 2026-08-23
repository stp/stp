; QF_AX selects declared scalar sorts and extensional array equality without
; either of STP's nonstandard feature flags. These queries cover the shapes in
; the SMT-LIB QF_AX corpus: select/store, whole-array equality, an extensional
; disequality witness, and conditional store commutativity.
;
; RUN: %solver --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --incremental=on  %s 2>&1 | %OutputCheck %s
; CHECK-NOT: unsupported
; CHECK-NOT: error
; CHECK: ^unsat
; CHECK: ^sat
; CHECK: ^unsat
; CHECK: ^unsat
; CHECK: QF-AX-DONE
;
(set-logic QF_AX)
(declare-sort Index 0)
(declare-sort Element 0)
(declare-fun a () (Array Index Element))
(declare-fun b () (Array Index Element))
(declare-fun i () Index)
(declare-fun j () Index)
(declare-fun e () Element)
(declare-fun f () Element)

; Equal arrays agree at every index.
(push 1)
(assert (= a b))
(assert (not (= (select a i) (select b i))))
(check-sat)
(pop 1)

; Agreement at one named index does not make two arrays equal: the
; extensionality witness can select another index.
(push 1)
(assert (not (= a b)))
(assert (= (select a i) (select b i)))
(check-sat)
(pop 1)

; Read-over-write uses Element as a value sort, not its carrier sort.
(push 1)
(assert (not (= (select (store a i e) i) e)))
(check-sat)
(pop 1)

; Stores at distinct indices commute as whole arrays.
(push 1)
(assert (not (= i j)))
(assert (not (= (store (store a i e) j f)
                (store (store a j f) i e))))
(check-sat)
(pop 1)

(echo "QF-AX-DONE")
