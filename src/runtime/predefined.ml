
(************************)
(* Built-in Definitions *)
(************************)

let name_alpha = Name.make (Name.greek 0)

let predefined_aml_types = let open Input in
  let loc = Location.unknown in
  let ty_alpha = ML_TyApply (name_alpha, []), loc in
  let decl_option = DefMLType [Name.Predefined.option, ([name_alpha],
    ML_Sum [
    (Name.Predefined.none, []);
    (Name.Predefined.some, [ty_alpha])
    ])], loc
  and decl_list = DefMLTypeRec [Name.Predefined.list, ([name_alpha],
    ML_Sum [
    (Name.Predefined.nil, []);
    (Name.Predefined.cons, [ty_alpha; (ML_TyApply (Name.Predefined.list, [ty_alpha]), loc)])
    ])], loc
  in
  [decl_option; decl_list]

let predefined_ops = (* let open Input in
  let loc = Location.unknown in *)
  []

let predefined_bound = let open Input in
  let loc = Location.unknown in
  let decl_hyps = TopDynamic (Name.Predefined.hypotheses, (List [], loc)), loc in
  let force_hyps_type = TopDo (Let ([Name.anonymous (), [],
    Some (ML_Forall ([], (ML_TyApply (Name.Predefined.list, [ML_Judgment, loc]) , loc)), loc),
    (Var Name.Predefined.hypotheses, loc)], (Tuple [], loc)), loc), loc in
  [decl_hyps; force_hyps_type]

let predefined_bound_names =
  [Name.Predefined.hypotheses]

let aml_definitions = List.concat [predefined_aml_types; predefined_ops; predefined_bound]


(************************)
(* AML list <-> ML list *)
(************************)

let list_nil        = Runtime.mk_tag Name.Predefined.nil []
let list_cons v lst = Runtime.mk_tag Name.Predefined.cons [v; lst]

let rec mk_list = function
  | []      -> list_nil
  | x :: xs -> list_cons x (mk_list xs)

let as_list ~loc v =
  match Runtime.as_list_opt v with
  | Some lst -> lst
  | None -> Runtime.(error ~loc (ListExpected v))


(****************************)
(* AML option <-> ML option *)
(****************************)

let from_option = function
  | Some v -> Runtime.mk_tag Name.Predefined.some [v]
  | None -> Runtime.mk_tag Name.Predefined.none []

let as_option ~loc = function
  | Runtime.Tag (t,[]) when (Name.eq_ident t Name.Predefined.none)  -> None
  | Runtime.Tag (t,[x]) when (Name.eq_ident t Name.Predefined.some) -> Some x
  | (Runtime.Term _ | Runtime.Closure _ | Runtime.Handler _ | Runtime.Tag _ | Runtime.Tuple _ |
     Runtime.Ref _ | Runtime.String _) as v ->
     Runtime.(error ~loc (OptionExpected v))


(*********)
(* Other *)
(*********)

(* Possibly this should be in Runtime?
   It seems to be here only because predefined_bound_names
   isn't in the interface.
*)

let add_abstracting j m =
  let (>>=) = Runtime.bind in
  let loc = Location.unknown in
  (* In practice k will be 0 because hypothesis is the first dynamic variable *)
  let k = match Name.level_of_ident Name.Predefined.hypotheses predefined_bound_names with
    | Some k -> k
    | None -> assert false
  in
  let v = Runtime.mk_term j in                  (* The given variable as an AML value *)
  Runtime.index_of_level k >>= fun k ->         (* Switch k from counting from the
                                                   beginning to counting from the end *)
  Runtime.lookup_bound ~loc k >>= fun hyps ->   (* Get the AML list of [hypotheses] *)
  let hyps = list_cons v hyps in                (* Add v to the front of that AML list *)
  Runtime.now ~loc k hyps m                     (* Run computation m in this dynamic scope *)

