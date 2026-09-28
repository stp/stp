; The ordering rewrite works over a sort declared by declare-sort, which is what
; the kind gate was widened for. Twenty constants, so the file stays readable;
; the size at which the rewrite starts mattering is well below that, and this is
; not a timing test.
;
; Elements of such a sort are ordered for the same reason bit-vectors are: bit
; equality on the carrier is the sort's own equality, so the unsigned order over
; the carrier is a total order on the elements and requiring the operands to
; increase discards n!-1 copies of every answer. A float would not qualify --
; FP_SMT_EQ is not bit equality -- and a rounding mode has five elements and no
; reason to be ordered.
;
; What this does and does not pin is worth stating, because the obvious claim is
; not available. It does NOT discriminate against the version of STP before a
; declared sort had an identity: there the sort simply WAS a bit-vector, so the
; kind gate admitted it for the wrong reason and this file passed. Nor can the
; full-SourceSort comparison that replaced the width test be discriminated at
; all -- a distinct mixing two sorts is a sort error before this pass ever sees
; it, so that comparison is defence-in-depth and not enforcement.
;
; What it does pin is that the gate still admits the kind. Removing
; Kind::Uninterpreted from it compiles, leaves every other test in the suite
; green, and silently costs this shape the rewrite -- verified by making that
; edit and watching this file fail. The second RUN is the control: with the
; feature off nothing is ordered, so the first RUN's line cannot be background
; noise.
;
; RUN: %solver --uninterpreted-functions --incremental=off -s %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=off -s --distinct-ordering=0 %s 2>&1 | %OutputCheck --check-prefix=OFF %s
;
; CHECK: Ordered 1 symmetric distinct group\(s\)
; CHECK: ^sat
; CHECK: BIG-DONE
; CHECK: Ordered 2 symmetric distinct group\(s\)
; CHECK: ^sat
;
; OFF-NOT: Ordered
; OFF: BIG-DONE
;
(set-logic QF_UFBV)
(declare-sort S 0)
(declare-fun e0 () S)
(declare-fun e1 () S)
(declare-fun e2 () S)
(declare-fun e3 () S)
(declare-fun e4 () S)
(declare-fun e5 () S)
(declare-fun e6 () S)
(declare-fun e7 () S)
(declare-fun e8 () S)
(declare-fun e9 () S)
(declare-fun e10 () S)
(declare-fun e11 () S)
(declare-fun e12 () S)
(declare-fun e13 () S)
(declare-fun e14 () S)
(declare-fun e15 () S)
(declare-fun e16 () S)
(declare-fun e17 () S)
(declare-fun e18 () S)
(declare-fun e19 () S)
(assert (distinct e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19))
(check-sat)
(echo "BIG-DONE")
(reset)
(set-logic QF_UFBV)
(declare-sort S 0)
(declare-sort T 0)
(declare-fun s0 () S)
(declare-fun s1 () S)
(declare-fun s2 () S)
(declare-fun t0 () T)
(declare-fun t1 () T)
(declare-fun t2 () T)
(assert (distinct s0 s1 s2))
(assert (distinct t0 t1 t2))
(check-sat)
