


(** The ML equivalent of the AML coercible type
 *)
type coercible =
  | NotCoercible
  | Convertible of Jdg.eq_ty
  | Coercible of Jdg.term


val definitions : Input.toplevel list

(** {6 Runtime computations to invoke operations} *)

(** A computation that, when run, invokes the [equal] operation on the given
    terms (wrapped as AML values), and then returns the resulting term if any
    (unwrapped from an AML value
    to a type theoretical judgment
 *)
val operation_equal : loc:Location.t -> Jdg.term -> Jdg.term -> Jdg.term option Runtime.comp

(** A computation that, when run, invokes the [coerce] operation
    on the given type theory term and desired type, and decodes
    the resulting AML value as a value of the correponding ML type [coercible].
 *)
val operation_coerce : loc:Location.t -> Jdg.term -> Jdg.ty -> coercible Runtime.comp

(** A computation that, when run, invokes the [coerce_fun] operation on the
    given term and decodes the resulting AML value into the ML type [coercible].
 *)
val operation_coerce_fun : loc:Location.t -> Jdg.term -> coercible Runtime.comp

(** A computation that, when run, invokes the [as_prod] operration on the
    given type; unwraps the resulting evidence (if any) that the given
    type is equal to a Pi type.
 *)
val operation_as_prod : loc:Location.t -> Jdg.ty -> Jdg.term option Runtime.comp

(** A computation that, when run, invokes the [as_eq] operration on the
    given type; unwraps the resulting evidence (if any) that the given
    type is equal to an == type.
 *)
val operation_as_eq : loc:Location.t -> Jdg.ty -> Jdg.term option Runtime.comp


