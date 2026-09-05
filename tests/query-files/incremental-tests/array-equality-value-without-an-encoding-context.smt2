; get-value of an equality between two float-indexed arrays the solve never
; encoded, under the incremental driver.
;
; The sibling case is fp-get-value-with-no-fp-in-the-query.smt2: same defect,
; same fix, and the other of the two places that read the published
; floating-point encoding context. That one asks for a float term's value and
; reaches requireFpEncodingContext; this one asks whether two arrays are equal
; and reaches arrayEqualityIsModelDecidable, which reads the same pointer
; through a gate of its own and answered:
;
;   STP Error: array-equality: cannot evaluate an opaque equality over
;              float-indexed arrays that was not reachable in the most
;              recent solve
;
; (Through the C API the same place is a FatalError, so it took the process
; down rather than reporting anything.)
;
; The driver built its encoding context lazily during encoding and published
; it only when it had one, so a solve with no float in the encoded formula
; left the model machinery holding NULL -- which already meant "no solve has
; run". Both readers then treated a query that had in fact been solved as
; though it had not. Publishing per solve, whether or not the stack has a
; float, is what fixed both.
;
; The two arms are independent and neither test stands in for the other: a
; fix that made requireFpEncodingContext conjure a context when it found none
; -- the alternative the fix commit weighed and rejected -- passes the sibling
; file and still aborts here, because the gate on this route reads the field
; and not the accessor.
;
; Three things have to line up, and they are the whole content of this file:
;
;   * the index sort is in the floating-point theory -- RoundingMode counts,
;     and no Float is needed anywhere;
;   * the solve does not encode the arrays, so no float reaches the encoder
;     and nothing builds a context; and
;   * a solve has actually run, so there is a model to read.
;
; Two rounds, because there are two ways to keep the arrays away from the
; encoder and only the second is the one the fuzzer found. The first never
; mentions them outside the get-value at all; the second mentions them in an
; assumption that is a tautology, which is rewritten away before encoding.
; The first does not depend on that rewrite happening, so it still exercises
; this site if the rewriter ever stops folding the second.
;
; |x| is pinned by a bit-vector assertion and asked for alongside, so that the
; run is anchored to a real model with a forced value in it: if a change ever
; made the check-sat vacuous, this file would fail rather than quietly stop
; testing anything. The equality itself answers true because neither array is
; in the model -- with no cells recorded against either, ArraysEqualUsingModel
; has no index to disagree at -- so it is the evaluator's answer to give and
; not the SAT search's, and the batch driver gives the same one. That is what
; the RUN lines below check by putting one set of expectations to both.
;
; --array-equality is required to build a whole-array equality at all;
; --incremental selects the affected driver, and the auto-engaged route
; reaches it without being asked.
;
; RUN: %solver --array-equality --incremental=on %s 2>&1 | %OutputCheck %s
; RUN: %solver --array-equality --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --array-equality --incremental-auto-engage-at 1 %s 2>&1 | %OutputCheck %s
(set-logic QF_ABVFP)
(set-option :produce-models true)
(declare-const a (Array RoundingMode RoundingMode))
(declare-const b (Array RoundingMode RoundingMode))
(declare-const x (_ BitVec 4))
; The only assertion in the file, and it names no array and no float.
(assert (= x #b0011))

; Round one: the arrays appear for the first time in the get-value.
; CHECK: ^sat$
(check-sat)
; (CHECK-L because the echoed terms hold regex metacharacters.)
; CHECK-L: ( (= |a| |b|) true )
; CHECK-L: ( |x|  #x3 )
(get-value ((= a b) x))

; Round two: the reproducer as filed. The assumption is a tautology, so it is
; rewritten away and the arrays still never reach the encoder.
; CHECK: ^sat$
(check-sat-assuming ((=> (= a b) (= a b))))
; CHECK-L: ( (= |a| |b|) true )
; CHECK-L: ( |x|  #x3 )
(get-value ((= a b) x))

; Both rounds answered, so nothing below the last match may be an error.
; CHECK-NOT: Fatal Error
; CHECK-NOT: STP Error
(exit)
