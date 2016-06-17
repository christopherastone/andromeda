(** Predefined types and operations. *)


(** {6 Built-in Definitions} *)

(** The list of AML-generic built-in type, operation, and dynamic variable definitions
    corresponding to the names in Name.Predeclared, e.g.,
       - ['a list] and its constructors [[]] and [::]
       - ['a option] and its constructors [Some] and [None]
       - the dynamic variable [hypotheses]
 *)
val aml_definitions : Input.toplevel list

(** {6 translation between AML and ML values} *)

(** Decodes an AML list value as an ML list of AML values.
    Fails if the given value is not an AML [list].
 *)
val as_list : loc:Location.t -> Runtime.value -> Runtime.value list

(** Encodes a list of AML values as an AML list value
 *)
val mk_list : Runtime.value list -> Runtime.value

(** Encodes an ML option as an AML option
 *)
val from_option : Runtime.value option -> Runtime.value

(** Decodes an AML option as an ML option.
    Fails if the given value is not an AML [option]
 *)
val as_option : loc:Location.t -> Runtime.value -> Runtime.value option

(** {6 Other} *)

(** Takes a variable (a judgment describing a variable/atom within a context),
    temporarily adds it to the the front of the list contained in the
    dynamic variable [hypotheses] to run the given computation.
 *)
val add_abstracting : Jdg.term -> 'a Runtime.comp -> 'a Runtime.comp

