**
* Owned and copyright BitBlaze, 2007. All rights reserved.*
** 

(**)
type vc = Libstp.vc (** The type of a validity checker *)
type exp = Libstp.expr (** The type of an STP expression *)
type typ = Libstp.typ (** The STP type of an STP expression *)

val create_validity_checker : unit -> vc
  (** Creates a new validity checker *)

val bool_t : vc -> typ
  (** Create a boolean type *)

val array_t : vc -> typ -> typ -> typ
  (** [array_t vc index_t data_t] creates a new array type
      @param vc the validity checker in which the result will be used.
      @param index_t the type of the array indices.
      @param data_t the type of the array elements.
  *)

val bitvector_t : vc -> int -> typ
  (** Create a bitvector type *)

val e_var : vc -> string -> typ -> exp
  (** Create a variable *)

val e_eq : vc -> exp -> exp -> exp
  (** Create an equality expression (e1 = e2) *)

val e_true : vc -> exp
  (** Create a true expression (TRUE) *)

val e_false : vc -> exp
  (** Create a false expression (FALSE) *)

val e_not : vc -> exp -> exp
  (** Create a not expression (NOT(e1)) *)

val e_and : vc -> exp -> exp -> exp
val e_or : vc -> exp -> exp -> exp
val e_implies : vc -> exp -> exp -> exp
val e_iff : vc -> exp -> exp -> exp
val e_ite : vc -> exp -> exp -> exp -> exp
val e_boolbv : vc -> exp -> exp
(** Create a one bit bitvector out of a boolean *)

val e_read : vc -> exp -> exp -> exp
  (** Read memory. 
     [e_read vc array index] will return the [index]th element of [array].
  *)

val e_write : vc -> exp -> exp -> exp -> exp
  (** Write to memory. 
      [e_write vc array index new_val] will return an array just like [array],
      but with array\[index\] set to new_val.
  *)

val e_bv_of_string : vc -> string -> exp
  (** Create a bitvector by parsing the given string *)
val e_bv_of_int : vc -> int -> int -> exp
  (** Create a bitvector from the given int *)
val e_bv_of_int32 : vc -> int32 -> exp
  (** Create a 32-bit bitvector from the given int32 *)
val e_bv_of_int64 : vc -> int -> int64 -> exp
  (** Create a bitvectr from the given int64 *)

val e_bvconcat : vc -> exp -> exp -> exp

val e_bvplus : vc -> int -> exp -> exp -> exp
val e_bvminus : vc -> int -> exp -> exp -> exp
val e_bvmult : vc -> int -> exp -> exp -> exp
val e_bvdiv : vc -> int -> exp -> exp -> exp
val e_bvmod : vc -> int -> exp -> exp -> exp
val e_bvand : vc -> exp -> exp -> exp
val e_bvor : vc -> exp -> exp -> exp
val e_bvxor : vc -> exp -> exp -> exp
val e_bvneg : vc -> exp -> exp
val e_bvnot : vc -> exp -> exp
val e_bvextract : vc -> exp -> int -> int -> exp
  (** Extract a range of bits from a bitvector *)
val e_bvbitextract : vc ->  exp -> int -> exp
  (** Extract a boolean from a bitvector *)

val e_bvsextend : vc -> int -> exp -> exp
val e_bvconstshiftleft : vc -> int -> exp -> int -> exp
val e_bvconstshiftright : vc -> int -> exp -> int -> exp
val e_bvconstshiftright_arith : vc -> int -> exp -> int -> exp
val e_bvshiftleft : vc -> int -> exp -> int->exp -> exp
val e_bvshiftright : vc -> int -> exp -> int->exp -> exp
val e_bvshiftright_arith : vc -> int -> exp -> int-> exp -> exp
val e_bvlt : vc -> exp -> exp -> exp
val e_bvle : vc -> exp -> exp -> exp
val e_bvgt : vc -> exp -> exp -> exp
val e_bvge : vc -> exp -> exp -> exp
val e_bvslt : vc -> exp -> exp -> exp
val e_bvsle : vc -> exp -> exp -> exp
val e_bvsgt : vc -> exp -> exp -> exp
val e_bvsge : vc -> exp -> exp -> exp

val do_assert : vc -> exp -> unit
  (** Assert an expression in the VC *)
val e_simplify : vc -> exp -> exp
  (** Simplify an expression *)

val query : vc -> exp -> bool
  (** Query the VC.
      @return true if the expression can be proven,
      or false if there is a counterexample, in which case the context of the
      VC is set to be the counterexample.
  *)

val get_counterexample : vc -> exp -> exp
  (** Evaluate the given expression in the context of the counterexample *)

val int_of_e : exp -> int
  (** Convert a constant bitvector expression into an int *)
val int64_of_e : exp -> int64
  (** Convert a constant bitvector expression into an int64 *)


val to_string : exp -> string
  (** @return the string representation of the given expression *)

val type_to_string : typ -> string
  (** @return the string representation of the given type *)
