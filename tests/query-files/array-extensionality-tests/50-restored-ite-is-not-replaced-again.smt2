; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK: ^unsat
; An array if-then-else nested inside a store inside another array
; if-then-else, with no array equality anywhere -- the same class as
; test 47, at the nesting depth that made a defect visible.
;
; While every if-then-else was replaced at construction, a query like
; this one had to have the replacements undone again, and the undoing
; re-entered the node factory: substituting the expansions back in
; rebuilds any node whose children changed, and an if-then-else whose
; branch still mentions an inner replacement is such a node, so it was
; replaced all over again. Nothing defined the replacement minted
; there, and the solved formula carried a free array: this query
; answered sat. It depended on the order the replacements came out of
; their map, which is why 250 queries of the class did not find it --
; declaring q before p expanded the inner one first and the answer came
; out right by luck.
;
; There is nothing to undo now, so there is no second rewriting to get
; wrong. Kept as coverage of the shape.
;
; Unsat because select of the outer if-then-else at #x0 is #x11 when p
; (the store put it there) and b[#x0] otherwise, which is asserted to
; be #x11 as well.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun b () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun p () Bool)
(declare-fun q () Bool)
(assert (distinct (select (ite p (store (ite q a b) #x0 #x11) b) #x0) #x11))
(assert (= (select b #x0) #x11))
(check-sat)
