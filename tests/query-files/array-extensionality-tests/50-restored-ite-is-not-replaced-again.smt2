; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK: ^unsat
; An array if-then-else nested inside a store inside another array
; if-then-else, with no array equality anywhere -- so restoreArrayITEs
; puts both back and the classic path decides the query.
;
; Restoring expands each replacement into the if-then-else it stands
; for and then substitutes those into the formula. The substitution
; rebuilds any node whose children changed, and the outer if-then-else
; still mentions the inner replacement whenever the registry hands the
; outer one out first -- so the rebuilt node went back through the node
; factory with the replacement hook still live and was replaced all
; over again. Nothing defines a replacement minted there:
; conjoinRecordConstraints emits the guards only while the procedure is
; active, and the whole point of this path is that it is not. The
; solved formula was left with a free array, and this query answered
; sat.
;
; The same root cause also aborted on assert(arrayops): the two
; restorations of the same formula saw different registries, so the
; candidate was judged against arrays the solved formula no longer
; contained.
;
; Sensitive to the order the registry's map yields its replacements,
; which is why 250 queries of this class did not find it -- declaring q
; before p expands the inner one first, no rebuild happens, and the
; answer is right by luck.
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
