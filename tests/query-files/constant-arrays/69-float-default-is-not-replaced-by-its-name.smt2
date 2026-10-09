; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --incremental=on %s | %OutputCheck %s
; RUN: %solver --incremental=off %s | %OutputCheck %s
; RUN: %solver -d %s | %OutputCheck %s
; The array equality, though over another array, brings in the array-equality
; procedure. It names the constant array's default x with a fresh bit-vector
; symbol and defines the name by "name = x". Equality propagation used that
; definition backwards and replaced the float x by its name everywhere, before
; floating-point lowering, so fp.isNegative reached the bit-blaster over an
; operand that was no longer a float and STP aborted, and in the equality
; below FloatBlast met one float and one bit-vector and refused the query. A
; float may only be replaced by a term of its own sort.
(set-option :produce-models true)
(set-logic QF_ABVFP)
(declare-fun x () (_ FloatingPoint 5 11))
(declare-fun b () (_ BitVec 1))
(declare-fun a () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun i () (_ BitVec 2))
(declare-fun j () (_ BitVec 2))
(assert (= (store a i #b00) (store a j #b00)))
(assert (fp.isNegative x))
(push 1)
; The read is +0 at index 1 and the negative x elsewhere.
(assert (fp.isPositive
  (select (store ((as const (Array (_ BitVec 1) (_ FloatingPoint 5 11))) x)
                 #b1 (_ +zero 5 11))
          b)))
; CHECK: ^sat$
(check-sat)
; CHECK: \(b #b1\)
(get-value (b))
(assert (= b #b0))
; CHECK: ^unsat$
(check-sat)
(pop 1)
(push 1)
(assert (= (select (store ((as const (Array (_ BitVec 1) (_ FloatingPoint 5 11))) x)
                          #b1 (_ +zero 5 11))
                   b)
           x))
; CHECK: ^sat$
(check-sat)
; CHECK: \(b #b0\)
(get-value (b))
(pop 1)
