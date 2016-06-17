(** The ML equivalent of the AML coercible type
 *)
type coercible =
  | NotCoercible
  | Convertible of Jdg.eq_ty
  | Coercible of Jdg.term

let types = let open Input in
  let loc = Location.unknown in

  let decl_coercible = DefMLType [Name.Predefined.coercible_ty, ([],
    ML_Sum [
    (Name.Predefined.notcoercible, []);
    (Name.Predefined.convertible, [ML_Judgment, loc]);
    (Name.Predefined.coercible_constructor, [ML_Judgment, loc])
    ])], loc
  in
    [decl_coercible]

let ops = let open Input in
  let loc = Location.unknown in
  let decl_equal = DeclOperation (Name.Predefined.equal, ([ML_Judgment, loc; ML_Judgment, loc], (ML_TyApply (Name.Predefined.option, [ML_Judgment, loc]), loc))), loc
  and decl_as_prod = DeclOperation (Name.Predefined.as_prod, ([ML_Judgment, loc], (ML_TyApply (Name.Predefined.option, [ML_Judgment, loc]), loc))), loc
  and decl_as_eq = DeclOperation (Name.Predefined.as_eq, ([ML_Judgment, loc], (ML_TyApply (Name.Predefined.option, [ML_Judgment, loc]), loc))), loc
  and decl_coerce = DeclOperation (Name.Predefined.coerce, ([ML_Judgment, loc; ML_Judgment, loc], (ML_TyApply (Name.Predefined.coercible_ty, []), loc))), loc
  and decl_coerce_fun = DeclOperation (Name.Predefined.coerce_fun, ([ML_Judgment, loc], (ML_TyApply (Name.Predefined.coercible_ty, []), loc))), loc
  in
  [decl_equal; decl_as_prod; decl_as_eq; decl_coerce; decl_coerce_fun]

let definitions = List.concat [Predefined.aml_definitions; types; ops]

(**********************************)
(* AML coercible <-> ML coercible *)
(**********************************)

let as_coercible ~loc = function
  | Runtime.Tag (t, []) when Name.eq_ident t Name.Predefined.notcoercible ->
    NotCoercible
  | Runtime.Tag (t, [v]) when Name.eq_ident t Name.Predefined.convertible ->
    let j = Runtime.as_term ~loc v in
    let jeq = Jdg.reflect_ty_eq ~loc j in
    Convertible jeq
  | Runtime.Tag (t, [v]) when Name.eq_ident t Name.Predefined.coercible_constructor ->
    let j = Runtime.as_term ~loc v in
    Coercible j
  | (Runtime.Term _ | Runtime.Closure _ | Runtime.Handler _ | Runtime.Tag _ | Runtime.Tuple _ |
     Runtime.Ref _ | Runtime.String _) as v ->
     Runtime.(error ~loc (CoercibleExpected v))


(***************************************)
(* Computations that invoke operations *)
(***************************************)

(* Maps AML-value-to-(term)-judgment across an option.
   Fails if given Some value that is not a judgment.
 *)
let as_term_option ~loc v =
  match Predefined.as_option ~loc v with
    | Some v -> Some (Runtime.as_term ~loc v)
    | None -> None

let (>>=) = Runtime.bind

let operation_equal ~loc j1 j2 =
  let v1 = Runtime.mk_term j1
  and v2 = Runtime.mk_term j2 in
  Runtime.operation Name.Predefined.equal [v1;v2] >>= fun v ->
  Runtime.return (as_term_option ~loc v)

let operation_coerce ~loc j1 j2 =
  let v1 = Runtime.mk_term j1
  and v2 = Runtime.mk_term (Jdg.term_of_ty j2) in
  Runtime.operation Name.Predefined.coerce [v1;v2] >>= fun v ->
  Runtime.return (as_coercible ~loc v)

let operation_coerce_fun ~loc j =
  let v = Runtime.mk_term j in
  Runtime.operation Name.Predefined.coerce_fun [v] >>= fun v ->
  Runtime.return (as_coercible ~loc v)

let operation_as_prod ~loc j =
  let v = Runtime.mk_term (Jdg.term_of_ty j) in
  Runtime.operation Name.Predefined.as_prod [v] >>= fun v ->
  Runtime.return (as_term_option ~loc v)

let operation_as_eq ~loc j =
  let v = Runtime.mk_term (Jdg.term_of_ty j) in
  Runtime.operation Name.Predefined.as_eq [v] >>= fun v ->
  Runtime.return (as_term_option ~loc v)



