; The candidate counter counts operations, not bit-blaster visits.
;
; bv_candidates is documented as the operations that reached the bit-blaster at
; or above the width floor -- what the abstraction COULD have taken -- and it
; exists so that a flag which found nothing eligible can be told from a flag
; that is broken. It was incremented at the top of each abstraction arm, which
; is a visit: this driver clears its term memo on every new root, so one
; operation is re-entered once per check-sat, while bv_abstracted correctly
; counts the one record that was minted for it.
;
; Ten solves over the one multiplication below therefore read mult=10->1, which
; says the abstraction took a tenth of what it could have. It took all of it.
; The ratio reaches vc_getCounter and every profile comparison run over an
; incremental corpus, so a number that degrades linearly with session length is
; not a number those comparisons can use.
;
; Counted once per operation, the ratio means what it says and carries an
; invariant with it: abstracted can never exceed candidates, so a second record
; for one operation shows as 1->2 rather than hiding inside a larger left
; number. That is what the sibling fixture on predicate canonicalisation now
; checks.
;
; Only the multiplication's field is pinned. The pushed assertions are eight
; bits wide and below the abstraction floor, but the driver's own encoding puts
; one wide equality in front of the counters, and what that equality is is not
; what this fixture is about; pinning the whole line would make it a test of
; the encoding's shape.
;
; RUN: %solver --incremental=on -d -t --bv-term-abstraction=1 --bv-term-abstraction-compare=0 %s 2>&1 | %OutputCheck --check-prefix=ONCE %s
;
; ONCE: Abstraction coverage \(candidates -> abstracted\):.* mult=1->1
; ONCE: ^sat$
(set-logic QF_BV)
(declare-fun x () (_ BitVec 64))
(declare-fun y () (_ BitVec 64))
(declare-fun w () (_ BitVec 8))
(assert (bvult (bvmul x y) (_ bv18446744073709551615 64)))
(push 1)
(assert (= w (_ bv1 8)))
(check-sat)
(pop 1)
(push 1)
(assert (= w (_ bv2 8)))
(check-sat)
(pop 1)
(push 1)
(assert (= w (_ bv3 8)))
(check-sat)
(pop 1)
(push 1)
(assert (= w (_ bv4 8)))
(check-sat)
(pop 1)
(push 1)
(assert (= w (_ bv5 8)))
(check-sat)
(pop 1)
(push 1)
(assert (= w (_ bv6 8)))
(check-sat)
(pop 1)
(push 1)
(assert (= w (_ bv7 8)))
(check-sat)
(pop 1)
(push 1)
(assert (= w (_ bv8 8)))
(check-sat)
(pop 1)
(push 1)
(assert (= w (_ bv9 8)))
(check-sat)
(pop 1)
(push 1)
(assert (= w (_ bv10 8)))
(check-sat)
(pop 1)
(exit)
