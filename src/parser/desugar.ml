(** Conversion from sugared to desugared input syntax *)

(** A let-bound name has lexical scoping and a dynamic-bound name dynamic scoping. *)
type scoping =
  | Lexical
  | Dynamic

(** The arity of an operation or a data constructor. *)
type arity = int

type unknown = Unknown

(** Information about names *)
type 'index info =
  | Variable of 'index * scoping
  | Constant
  | Constructor of arity
  | Operation of arity

let print_info info ppf = match info with
  | Variable (_, Lexical) -> Format.fprintf ppf "a lexical variable"
  | Variable (_, Dynamic) -> Format.fprintf ppf "a dynamic variable"
  | Constant -> Format.fprintf ppf "a constant"
  | Constructor _ -> Format.fprintf ppf "an AML constructor"
  | Operation _ -> Format.fprintf ppf "an operation"

type error =
  | UnknownName of Name.ident
  | UnknownTypeName of Name.ident
  | DynamicExpected : Name.ident * 'a info -> error
  | OperationExpected : Name.ident * 'a info -> error
  | ConstantAlreadyDeclared of Name.ident
  | OperationAlreadyDeclared of Name.ident
  | ConstructorAlreadyDeclared of Name.ident
  | InvalidTermPatternName : Name.ident * 'a info -> error
  | InvalidPatternName : Name.ident * 'a info -> error
  | InvalidAppliedPatternName : Name.ident * 'a info -> error
  | ArityMismatch of Name.ident * int * int
  | UnboundYield
  | ParallelShadowing of Name.ident
  | AppliedTyParam

let print_error err ppf = match err with
  | UnknownName x -> Format.fprintf ppf "Unknown name %t." (Name.print_ident x)
  | UnknownTypeName x -> Format.fprintf ppf "Unknown type name %t." (Name.print_ident x)
  | DynamicExpected (x,info) -> Format.fprintf ppf "%t should be a dynamic variable, but is %t." (Name.print_ident x) (print_info info)
  | OperationExpected (x, info) -> Format.fprintf ppf "%t should be an operation, but is %t." (Name.print_ident x) (print_info info)
  | ConstantAlreadyDeclared x -> Format.fprintf ppf "A constant %t is already declared." (Name.print_ident x)
  | OperationAlreadyDeclared x -> Format.fprintf ppf "An operation %t is already declared." (Name.print_ident x)
  | ConstructorAlreadyDeclared x -> Format.fprintf ppf "An AML constructor %t is already declared." (Name.print_ident x)
  | InvalidTermPatternName (x, info) -> Format.fprintf ppf "%t cannot be used in a term pattern as it is %t." (Name.print_ident x) (print_info info)
  | InvalidPatternName (x, info) -> Format.fprintf ppf "%t cannot be used in a pattern as it is %t." (Name.print_ident x) (print_info info)
  | InvalidAppliedPatternName (x, info) -> Format.fprintf ppf "%t cannot be applied in a pattern as it is %t." (Name.print_ident x) (print_info info)
  | ArityMismatch (x, used, expected) -> Format.fprintf ppf "%t expects %d arguments but is used with %d." (Name.print_ident x) expected used
  | UnboundYield -> Format.fprintf ppf "yield may only appear in a handler's operation cases."
  | ParallelShadowing x -> Format.fprintf ppf "%t is bound more than once." (Name.print_ident x)
  | AppliedTyParam -> Format.fprintf ppf "AML type parameters cannot be applied."

exception Error of error Location.located

let error ~loc err = Pervasives.raise (Error (Location.locate err loc))

(** Ctx variable management *)
module Ctx = struct

  type t = {
      bound : (Name.ident * unknown info) list;
      tydefs : (Name.ident * arity) list;
      files : string list;
    }

  let empty = {
      bound = [];
      tydefs = [];
      files = [];
    }


  let find ~loc x {bound; _} =
    let at_index i = function
      | Variable (Unknown, s) -> Variable (i, s)
      | Constant -> Constant
      | Constructor k -> Constructor k
      | Operation k -> Operation k
    in
    let rec search i = function
      | [] -> error ~loc (UnknownName x)
      | (y, info) :: _ when Name.eq_ident y x -> at_index i info
      | (_, Variable _) :: bound -> search (i+1) bound
      | (_, (Constant | Constructor _ | Operation _)) :: bound ->
         search i bound
    in
    search 0 bound

  let get_dynamic ~loc x ctx =
    match find ~loc x ctx with
    | Variable (i, Dynamic) -> i
    | Variable (_, Lexical) | Constant | Operation _ | Constructor _ as info ->
      error ~loc (DynamicExpected (x, info))

  let get_operation ~loc x ctx =
    match find ~loc x ctx with
    | Operation k -> k
    | Variable _ | Constant | Constructor _ as info ->
      error ~loc (OperationExpected (x, info))

  let add_lexical x ctx =
    { ctx with bound = (x, Variable (Unknown, Lexical)) :: ctx.bound }

  let add_dynamic x ctx =
    { ctx with bound = (x, Variable (Unknown, Dynamic)) :: ctx.bound }

  let add_operation ~loc op k ctx =
    if List.exists (function (op', Operation _) -> Name.eq_ident op op' | _ -> false) ctx.bound
    then
      error ~loc (OperationAlreadyDeclared op)
    else
      { ctx with bound = (op, Operation k) :: ctx.bound }

  let add_constructor ~loc c k ctx =
    if List.exists (function (c', Constructor _) -> Name.eq_ident c c' | _ -> false) ctx.bound
    then
      error ~loc (ConstructorAlreadyDeclared c)
    else
      { ctx with bound = (c, Constructor k) :: ctx.bound }

  let add_constant ~loc c ctx =
    if List.exists (function (c', Constant) -> Name.eq_ident c c' | _ -> false) ctx.bound
    then
      error ~loc (ConstantAlreadyDeclared c)
    else
      { ctx with bound = (c, Constant) :: ctx.bound }

  (* Add to the contex the fact that [ty] is a type constructor with
     [k] parameters. *)
  let add_tydef t k ctx =
    { ctx with tydefs = List.append ctx.tydefs [(t, k)] }

  (* Get the arity and de Bruijn level of type named [t] and its definition *)
  let get_tydef ~loc t {tydefs=lst; _} =
    let rec find k = function
      | [] -> error ~loc (UnknownTypeName t)
      | (u, arity) :: lst ->
         if Name.eq_ident t u
         then (k, arity)
         else find (k+1) lst
    in
    find 0 lst

  let push_file f ctx =
    { ctx with
      files = (Filename.basename f) :: ctx.files }

  let included f ctx =
    List.mem (Filename.basename f) ctx.files

end (* module Ctx *)

let locate = Location.locate

let mlty ctx params ty =
  (* Get the de Bruijn index of type parameter x *)
  let get_index x = Name.index_of_ident x params in

  let rec mlty (ty', loc) =
    let ty' =
      begin match ty' with

      | Input.ML_Arrow (ty1, ty2) ->
         let ty1 = mlty ty1
         and ty2 = mlty ty2 in
         Syntax.ML_Arrow (ty1, ty2)

      | Input.ML_Handler (ty1, ty2) ->
         let ty1 = mlty ty1
         and ty2 = mlty ty2 in
         Syntax.ML_Handler (ty1, ty2)

      | Input.ML_Prod tys ->
         let tys = List.map mlty tys in
         Syntax.ML_Prod tys

      | Input.ML_TyApply (x, args) ->
         begin
           match get_index x with
           | Some k ->
              (* It is a type parameter *)
              begin
                match args with
                | [] -> Syntax.ML_Bound k
                | _::_ -> error ~loc AppliedTyParam
              end
           | None ->
              (* It is a type name *)
              begin
                let (level, arity) = Ctx.get_tydef ~loc x ctx in
                let n = List.length args in
                if arity = n
                then
                  let args = List.map mlty args in
                  Syntax.ML_TyApply (x, level, args)
                else
                  error ~loc (ArityMismatch (x, n, arity))
              end
         end

      | Input.ML_Anonymous ->
         Syntax.ML_Anonymous

      | Input.ML_Judgment -> Syntax.ML_Judgment

      | Input.ML_String -> Syntax.ML_String
      end
    in
    locate ty' loc
  in
  mlty ty

(* TODO improve locs *)
let mk_lambda ~loc ys c =
  List.fold_left
    (fun c (y,u) -> locate (Syntax.Lambda (y,u,c)) loc)
    c ys

let mk_prod ~loc ys t =
  List.fold_left
    (fun c (y,u) -> locate (Syntax.Prod (y,u,c)) loc)
    t ys

(* n is the length of vars *)
let rec tt_pattern bound vars n (p,loc) =
  match p with
  | Input.Tt_Anonymous ->
     (locate Syntax.Tt_Anonymous loc), vars, n

  | Input.Tt_As (p,x) ->
     begin match Name.assoc_ident x vars with
     | Some i ->
        let p, vars, n = tt_pattern bound vars n p in
        (locate (Syntax.Tt_As (p,i)) loc), vars, n
     | None ->
        let i = n in
        let p, vars, n = tt_pattern bound ((x,n)::vars) (n+1) p in
        (locate (Syntax.Tt_As (p,i)) loc), vars, n
     end

  | Input.Tt_Var x ->
     begin match Name.assoc_ident x vars with
     | Some i ->
        locate (Syntax.Tt_As ((locate Syntax.Tt_Anonymous loc), i)) loc, vars, n
     | None ->
        locate (Syntax.Tt_As ((locate Syntax.Tt_Anonymous loc), n)) loc, ((x,n)::vars), (n+1)
     end

  | Input.Tt_Type ->
     (locate Syntax.Tt_Type loc), vars, n

  | Input.Tt_Name x ->
     begin match Ctx.find ~loc x bound with
     | Variable (i,_) -> locate (Syntax.Tt_Bound i) loc, vars, n
     | Constant -> locate (Syntax.Tt_Constant x) loc, vars, n
     | Constructor _ | Operation _ as info -> error ~loc (InvalidTermPatternName (x, info))
     end

  | Input.Tt_Lambda (b, x, popt, p) ->
     let popt, vars, n = match popt with
       | None ->
          None, vars, n
       | Some p ->
          let p, vars, n = tt_pattern bound vars n p in
          Some p, vars, n
     in
     let bopt, vars, n =
       if b
       then
         begin match Name.assoc_ident x vars with
         | Some i ->
            (* XXX it might be a good idea to warn if x is already
               a pattern variable, since that should never match. *)
            Some i, vars, n
         | None ->
            Some n, ((x,n)::vars), (n+1)
         end
       else None, vars, n
     in
     let p, vars, n = tt_pattern (Ctx.add_lexical x bound) vars n p in
     locate (Syntax.Tt_Lambda (x,bopt,popt,p)) loc, vars, n

  | Input.Tt_Apply (p1,p2) ->
     let p1, vars, n = tt_pattern bound vars n p1 in
     let p2, vars, n = tt_pattern bound vars n p2 in
     locate (Syntax.Tt_Apply (p1,p2)) loc, vars, n

  | Input.Tt_Prod (b,x,popt,p) ->
     let popt, vars, n = match popt with
       | None ->
          None, vars, n
       | Some p ->
          let p, vars, n = tt_pattern bound vars n p in
          Some p, vars, n
     in
     let bopt, vars, n =
       if b
       then
         begin match Name.assoc_ident x vars with
         | Some i ->
            (* XXX it might be a good idea to warn if x is already a pattern variable, since that should never match. *)
            Some i, vars, n
         | None ->
            Some n, ((x,n)::vars), (n+1)
         end
       else None, vars, n
     in
     let p, vars, n = tt_pattern (Ctx.add_lexical x bound) vars n p in
     locate (Syntax.Tt_Prod (x,bopt,popt,p)) loc, vars, n

  | Input.Tt_Eq (p1,p2) ->
     let p1, vars, n = tt_pattern bound vars n p1 in
     let p2, vars, n = tt_pattern bound vars n p2 in
     locate (Syntax.Tt_Eq (p1,p2)) loc, vars, n

  | Input.Tt_Refl p ->
     let p, vars, n = tt_pattern bound vars n p in
     locate (Syntax.Tt_Refl p) loc, vars, n

  | Input.Tt_GenAtom p ->
     let p, vars, n = tt_pattern bound vars n p in
     locate (Syntax.Tt_GenAtom p) loc, vars, n

  | Input.Tt_GenConstant p ->
     let p, vars, n = tt_pattern bound vars n p in
     locate (Syntax.Tt_GenConstant p) loc, vars, n

and pattern bound vars n (p,loc) =
  match p with
  | Input.Patt_Anonymous -> locate Syntax.Patt_Anonymous loc, vars, n

  | Input.Patt_As (p,x) ->
     begin match Name.assoc_ident x vars with
     | Some i ->
        let p, vars, n = pattern bound vars n p in
        locate (Syntax.Patt_As (p,i)) loc, vars, n
     | None ->
        let i = n in
        let p, vars, n = pattern bound ((x,i)::vars) (n+1) p in
        locate (Syntax.Patt_As (p,i)) loc, vars, n
     end

  | Input.Patt_Var x ->
     begin match Name.assoc_ident x vars with
     | Some i ->
        locate (Syntax.Patt_As (locate Syntax.Patt_Anonymous loc, i)) loc, vars, n
     | None ->
        locate (Syntax.Patt_As (locate Syntax.Patt_Anonymous loc, n)) loc, ((x,n)::vars), (n+1)
     end

  | Input.Patt_Name x ->
     begin match Ctx.find ~loc x bound with
     | Variable (i,_) ->
        locate (Syntax.Patt_Bound i) loc, vars, n
     | Constructor k ->
        if k = 0
        then locate (Syntax.Patt_Constructor (x,[])) loc, vars, n
        else error ~loc (ArityMismatch (x, 0, k))
     | Constant ->
        let p = locate (Syntax.Tt_Constant x) loc in
        let pt = locate Syntax.Tt_Anonymous loc in
        locate (Syntax.Patt_Jdg (p, pt)) loc, vars, n
     | Operation _ as info -> error ~loc (InvalidPatternName (x, info))
     end

  | Input.Patt_Jdg (p1,p2) ->
     let p1, vars, n = tt_pattern bound vars n p1 in
     let p2, vars, n = tt_pattern bound vars n p2 in
     locate (Syntax.Patt_Jdg (p1,p2)) loc, vars, n

  | Input.Patt_Constr (c,ps) ->
     begin match Ctx.find ~loc c bound with
     | Constructor k ->
        let len = List.length ps in
        if k = len
        then
          let rec fold vars n ps = function
            | [] ->
               let ps = List.rev ps in
               locate (Syntax.Patt_Constructor (c,ps)) loc, vars, n
            | p::rem ->
               let p, vars, n = pattern bound vars n p in
               fold vars n (p::ps) rem
          in
          fold vars n [] ps
        else
          error ~loc (ArityMismatch (c, n, k))
     | Variable _ | Constant | Operation _ as info ->
        error ~loc (InvalidAppliedPatternName (c, info))
     end

  | Input.Patt_List ps ->
     let rec fold ~loc vars n = function
       | [] -> locate (Syntax.Patt_Constructor (Name.Predefined.nil, [])) loc, vars, n
       | p :: ps ->
          let p, vars, n = pattern bound vars n p in
          let ps, vars, n = fold ~loc:(p.Location.loc) vars n ps in
          locate (Syntax.Patt_Constructor (Name.Predefined.cons, [p ; ps])) loc, vars, n
     in
     fold ~loc vars n ps

  | Input.Patt_Tuple ps ->
     let rec fold vars n ps = function
       | [] ->
          let ps = List.rev ps in
          locate (Syntax.Patt_Tuple ps) loc, vars, n
       | p::rem ->
          let p, vars, n = pattern bound vars n p in
          fold vars n (p::ps) rem
     in
     fold vars n [] ps

let rec comp ~yield bound (c',loc) =
  match c' with
  | Input.Handle (c, hcs) ->
     let c = comp ~yield bound c
     and h = handler ~loc bound hcs in
     locate (Syntax.With (h, c)) loc

  | Input.With (c1, c2) ->
     let c1 = comp ~yield bound c1
     and c2 = comp ~yield bound c2 in
     locate (Syntax.With (c1, c2)) loc

  | Input.Let (lst, c) ->
     let bound, lst = let_clauses ~loc ~yield bound lst in
     let c = comp ~yield bound c in
     locate (Syntax.Let (lst, c)) loc

  | Input.LetRec (lst, c) ->
     let bound, lst = letrec_clauses ~loc ~yield bound lst in
     let c = comp ~yield bound c in
     locate (Syntax.LetRec (lst, c)) loc

  | Input.Now (x,c1,c2) ->
     let y = Ctx.get_dynamic ~loc x bound
     and c1 = comp ~yield bound c1
     and c2 = comp ~yield bound c2 in
     locate (Syntax.Now (y,c1,c2)) loc

  | Input.Lookup c ->
     let c = comp ~yield bound c in
     locate (Syntax.Lookup c) loc

  | Input.Ref c ->
     let c = comp ~yield bound c in
     locate (Syntax.Ref c) loc

  | Input.Update (c1, c2) ->
     let c1 = comp ~yield bound c1
     and c2 = comp ~yield bound c2 in
     locate (Syntax.Update (c1, c2)) loc

  | Input.Sequence (c1, c2) ->
     let c1 = comp ~yield bound c1
     and c2 = comp ~yield bound c2 in
     locate (Syntax.Sequence (c1, c2)) loc

  | Input.Assume ((x, t), c) ->
     let t = comp ~yield bound t in
     let bound = Ctx.add_lexical x bound in
     let c = comp ~yield bound c in
     locate (Syntax.Assume ((x, t), c)) loc

  | Input.Where (c1, c2, c3) ->
     let c1 = comp ~yield bound c1
     and c2 = comp ~yield bound c2
     and c3 = comp ~yield bound c3 in
     locate (Syntax.Where (c1, c2, c3)) loc

  | Input.Match (c, cases) ->
     let c = comp ~yield bound c
     and cases = List.map (match_case ~yield bound) cases in
     locate (Syntax.Match (c, cases)) loc

  | Input.Ascribe (c, t) ->
     let t = comp ~yield bound t
     and c = comp ~yield bound c in
     locate (Syntax.Ascribe (c, t)) loc

  | Input.External s ->
     locate (Syntax.External s) loc

  | Input.Lambda (xs, c) ->
     let rec fold bound ys = function
       | [] ->
          let c = comp ~yield bound c in
          mk_lambda ~loc ys c
       | (x, None) :: xs ->
          let bound = Ctx.add_lexical x bound
          and ys = (x, None) :: ys in
          fold bound ys xs
       | (x, Some t) :: xs ->
          let ys = (let t = comp ~yield bound t in (x, Some t) :: ys)
          and bound = Ctx.add_lexical x bound in
          fold bound ys xs
     in
     fold bound [] xs

  | Input.Spine (e, cs) ->
     spine ~yield bound e cs

  | Input.Prod (xs, c) ->
     let rec fold bound ys = function
       | [] ->
          let c = comp ~yield bound c in
          mk_prod ~loc ys c
       | (x,t) :: xs ->
          let ys = (let t = comp ~yield bound t in (x, t) :: ys) in
          let bound = Ctx.add_lexical x bound in
          fold bound ys xs
     in
     fold bound [] xs

  | Input.Eq (c1, c2) ->
     let c1 = comp ~yield bound c1
     and c2 = comp ~yield bound c2 in
     locate (Syntax.Eq (c1, c2)) loc

  | Input.Refl c ->
     let c = comp ~yield bound c in
     locate (Syntax.Refl c) loc

  | Input.Var x ->
     begin match Ctx.find ~loc x bound with
     | Variable (i,_) -> locate (Syntax.Bound i) loc
     | Constant -> locate (Syntax.Constant x) loc
     | Constructor k ->
        if k = 0 then locate (Syntax.Constructor (x, [])) loc
        else error ~loc (ArityMismatch (x, 0, k))
     | Operation k ->
        if k = 0 then locate (Syntax.Operation (x, [])) loc
        else error ~loc (ArityMismatch (x, 0, k))
     end

  | Input.Type ->
     locate Syntax.Type loc

  | Input.Yield c ->
     if yield
     then
       let c = comp ~yield bound c in
       locate (Syntax.Yield c) loc
     else
      error ~loc UnboundYield

  | Input.Function (xs, c) ->
     let rec fold bound = function
       | [] -> comp ~yield bound c
       | x :: xs ->
          let bound = Ctx.add_lexical x bound in
          let c = fold bound xs in
          locate (Syntax.Function (x, c)) loc
     in
     fold bound xs

  | Input.Handler hcs ->
     handler ~loc bound hcs

  | Input.List cs ->
     let rec fold ~loc = function
       | [] -> locate (Syntax.Constructor (Name.Predefined.nil, [])) loc
       | c :: cs ->
          let c = comp ~yield bound c in
          let cs = fold ~loc:(c.Location.loc) cs in
          locate (Syntax.Constructor (Name.Predefined.cons, [c ; cs])) loc
     in
     fold ~loc cs

  | Input.Tuple cs ->
     let lst = List.map (comp ~yield bound) cs in
     locate (Syntax.Tuple lst) loc

  | Input.CongrProd (e1, e2, e3) ->
     let e1 = comp ~yield bound e1
     and e2 = comp ~yield bound e2
     and e3 = comp ~yield bound e3 in
     locate (Syntax.CongrProd (e1, e2, e3)) loc

  | Input.CongrApply (e1, e2, e3, e4, e5) ->
     let e1 = comp ~yield bound e1
     and e2 = comp ~yield bound e2
     and e3 = comp ~yield bound e3
     and e4 = comp ~yield bound e4
     and e5 = comp ~yield bound e5 in
     locate (Syntax.CongrApply (e1, e2, e3, e4, e5)) loc

  | Input.CongrLambda (e1, e2, e3, e4) ->
     let e1 = comp ~yield bound e1
     and e2 = comp ~yield bound e2
     and e3 = comp ~yield bound e3
     and e4 = comp ~yield bound e4 in
     locate (Syntax.CongrLambda (e1, e2, e3, e4)) loc

  | Input.CongrEq (e1, e2, e3) ->
     let e1 = comp ~yield bound e1
     and e2 = comp ~yield bound e2
     and e3 = comp ~yield bound e3 in
     locate (Syntax.CongrEq (e1, e2, e3)) loc

  | Input.CongrRefl (e1, e2) ->
     let e1 = comp ~yield bound e1
     and e2 = comp ~yield bound e2 in
     locate (Syntax.CongrRefl (e1, e2)) loc

  | Input.BetaStep (e1, e2, e3, e4, e5) ->
     let e1 = comp ~yield bound e1
     and e2 = comp ~yield bound e2
     and e3 = comp ~yield bound e3
     and e4 = comp ~yield bound e4
     and e5 = comp ~yield bound e5 in
     locate (Syntax.BetaStep (e1, e2, e3, e4, e5)) loc

  | Input.String s ->
     locate (Syntax.String s) loc

  | Input.Context c ->
     let c = comp ~yield bound c in
     locate (Syntax.Context c) loc

  | Input.Occurs (c1,c2) ->
     let c1 = comp ~yield bound c1
     and c2 = comp ~yield bound c2 in
     locate (Syntax.Occurs (c1,c2)) loc

  | Input.Natural c ->
     let c = comp ~yield bound c in
     locate (Syntax.Natural c) loc

and let_clauses ~loc ~yield bound lst =
  let rec fold bound' lst' = function
    | [] ->
       let lst' = List.rev lst' in
       bound', lst'
    | (x, ys, t_opt, c) :: xcs ->
       if List.exists (fun (y, _, _, _) -> Name.eq_ident x y) xcs
       then
         error ~loc (ParallelShadowing x)
       else
         let c = let_clause ~yield bound ys c in
         let t_opt = match t_opt with
           | Some (Input.ML_Forall (params, t), loc) ->
             Some (locate (Syntax.ML_Forall (params, mlty bound params t)) loc)
           | None -> None
         in
         let bound' = Ctx.add_lexical x bound' in
         let lst' = (x, t_opt, c) :: lst' in
         fold bound' lst' xcs
  in
  fold bound [] lst

and letrec_clauses ~loc ~yield bound lst =
  let bound =
    List.fold_left (fun bound (f, _, _, _, _) -> Ctx.add_lexical f bound) bound lst
  in
  let rec fold lst' = function
    | [] ->
       let lst' = List.rev lst' in
       bound, lst'
    | (f, y, ys, t_opt, c) :: xcs ->
       if List.exists (fun (g, _, _, _, _) -> Name.eq_ident f g) xcs
       then
         error ~loc (ParallelShadowing f)
       else
         let y, c = letrec_clause ~yield bound y ys c in
         let t_opt = match t_opt with
           | Some (Input.ML_Forall (params, t), loc) ->
             Some (locate (Syntax.ML_Forall (params, mlty bound params t)) loc)
           | None -> None
         in
         let lst' = (f, y, t_opt, c) :: lst' in
         fold lst' xcs
  in
  fold [] lst

and let_clause ~yield bound ys c =
  let rec fold bound = function
    | [] ->       
       comp ~yield bound c
    | y :: ys ->
       let bound = Ctx.add_lexical y bound in
       let c = fold bound ys in
       locate (Syntax.Function (y, c)) (c.Location.loc) (* XXX improve location *)
  in
  fold bound ys

and letrec_clause ~yield bound y ys c =
  let bound = Ctx.add_lexical y bound in
  let c = let_clause ~yield bound ys c in
  y, c


(* Desugar a spine. This function is a bit messy because we need to untangle
   to env. But it's worth doing to make users happy. TODO outdated comment *)
and spine ~yield bound ((c',loc) as c) cs =

  (* Auxiliary function which splits a list into two parts with k
     elements in the first part. *)
  let split x k lst =
    let n = List.length lst in
    if n < k
    then
      error ~loc (ArityMismatch (x, n, k))
    else
    let rec split acc k lst =
      if k = 0 then
        List.rev acc, lst
      else
        match lst with
        | [] -> assert false
        | x :: lst -> split (x :: acc) (k - 1) lst
    in
    split [] k lst
  in

  (* First we calculate the head of the spine, and the remaining arguments. *)
  let c, cs =
    match c' with
    | Input.Var x ->
       begin match Ctx.find ~loc x bound with
       | Variable (i,_) ->
          locate (Syntax.Bound i) loc, cs
       | Constant ->
          locate (Syntax.Constant x) loc, cs
       | Constructor k ->
          let cs', cs = split x k cs in
          data ~loc ~yield bound x cs', cs
       | Operation k ->
          let cs', cs = split x k cs in
          operation ~loc ~yield bound x cs', cs
       end

    | _ -> comp ~yield bound c, cs
  in

  (* TODO improve locs *)
  List.fold_left (fun h c ->
      let c = comp ~yield bound c in
      locate (Syntax.Apply (h,c)) loc) c cs

(* Desugar handler cases. *)
and handler ~loc bound hcs =
  (* for every case | #op p => c we do #op binder => match binder with | p => c end *)
  let rec fold val_cases op_cases finally_cases = function
    | [] ->
       List.rev val_cases, Name.IdentMap.map List.rev op_cases, List.rev finally_cases

    | Input.CaseVal c :: hcs ->
       (* XXX if this handler is in a outer handler's operation case, should we use its yield?
          eg handle ... with | op => handler | val x => yield x end end *)
       let case = match_case ~yield:false bound c in
       fold (case::val_cases) op_cases finally_cases hcs

    | Input.CaseOp (op, ((ps,_,_) as c)) :: hcs ->
       let k = Ctx.get_operation ~loc op bound in
       let n = List.length ps in
       if n = k
       then
         let case = match_op_case ~yield:true bound c in
         let my_cases = try Name.IdentMap.find op op_cases with | Not_found -> [] in
         let my_cases = case::my_cases in
         fold val_cases (Name.IdentMap.add op my_cases op_cases) finally_cases hcs
       else
         error ~loc (ArityMismatch (op, n, k))

    | Input.CaseFinally c :: hcs ->
       let case = match_case ~yield:false bound c in
       fold val_cases op_cases (case::finally_cases) hcs

  in
  let handler_val, handler_ops, handler_finally = fold [] Name.IdentMap.empty [] hcs in
  locate (Syntax.Handler (Syntax.{ handler_val ; handler_ops ; handler_finally })) loc

(* Desugar a match case *)
and match_case ~yield bound (p, c) =
  let p, vars, _ = pattern bound [] 0 p in
  let rec fold xs bound = function
    | [] -> xs, bound
    | (x,_)::rem -> fold (x::xs) (Ctx.add_lexical x bound) rem
  in
  let xs, bound = fold [] bound vars in
  let c = comp ~yield bound c in
  (xs, p, c)

and match_op_case ~yield bound (ps, pt, c) =
  let rec fold_patterns ps vars n = function
    | [] -> List.rev ps, vars, n
    | p::rem ->
       let p, vars, n = pattern bound vars n p in
       fold_patterns (p::ps) vars n rem
  in
  let ps, vars, n = fold_patterns [] [] 0 ps in
  let pt, vars = match pt with
    | Some p ->
       let p, vars, n = pattern bound vars n p in
       Some p, vars
    | None ->
       None, vars
  in
  let rec fold xs bound = function
    | [] -> xs, bound
    | (x,_)::rem -> fold (x::xs) (Ctx.add_lexical x bound) rem
  in
  let xs, bound = fold [] bound vars in
  let c = comp ~yield bound c in
  (xs, ps, pt, c)

and data ~loc ~yield bound x cs =
  let cs = List.map (comp ~yield bound) cs in
  locate (Syntax.Constructor (x, cs)) loc

and operation ~loc ~yield bound x cs =
  let cs = List.map (comp ~yield bound) cs in
  locate (Syntax.Operation (x, cs)) loc


let decl_operation ~loc ctx args res =
  let args = List.map (mlty ctx []) args
  and res = mlty ctx [] res in
  args, res


let mlty_def ~loc ctx outctx params def =
  match def with
  | Input.ML_Alias ty ->
     let ty = mlty ctx params ty in
     outctx, Syntax.ML_Alias ty
  | Input.ML_Sum lst ->
    let rec fold outctx res = function
      | [] -> outctx, Syntax.ML_Sum (List.rev res)
      | (c, args) :: lst ->
        let args = List.map (mlty ctx params) args in
        let outctx = Ctx.add_constructor ~loc c (List.length args) outctx in
        fold outctx ((c, args)::res) lst
    in
    fold outctx [] lst

let mlty_rec_def ~loc ctx params def =
  match def with
  | Input.ML_Alias ty ->
     let ty = mlty ctx params ty in
     ctx, Syntax.ML_Alias ty
  | Input.ML_Sum lst ->
    let rec fold ctx res = function
      | [] -> ctx, Syntax.ML_Sum (List.rev res)
      | (c, args) :: lst ->
        let args = List.map (mlty ctx params) args in
        let ctx = Ctx.add_constructor ~loc c (List.length args) ctx in
        fold ctx ((c, args)::res) lst
    in
    fold ctx [] lst

let mlty_defs ~loc ctx lst =
  let rec fold outctx res = function
    | [] -> outctx, List.rev res
    | (t, (params, def)) :: lst ->
      let outctx = Ctx.add_tydef t (List.length params) outctx in
      let outctx, def = mlty_def ~loc ctx outctx params def in
      fold outctx ((t, (params, def)) :: res) lst
  in
  fold ctx [] lst

let mlty_rec_defs ~loc ctx lst =
  let ctx = List.fold_left (fun ctx (t, (params,_)) -> Ctx.add_tydef t (List.length params) ctx) ctx lst in
  let rec fold ctx defs = function
    | [] -> (ctx, List.rev defs)
    | (t, (params, def)) :: lst ->
       if List.exists (fun (t', _) -> Name.eq_ident t t') lst
       then
         error ~loc (ParallelShadowing t)
       else
         let ctx, def = mlty_rec_def ~loc ctx params def in
         fold ctx ((t, (params, def)) :: defs) lst
  in
  fold ctx [] lst

let rec toplevel ~basedir ctx (cmd, loc) =
  match cmd with

    | Input.DeclOperation (op, (args, res)) ->
       let args, res = decl_operation ~loc ctx args res in
       let ctx = Ctx.add_operation ~loc op (List.length args) ctx in
       (ctx, locate (Syntax.DeclOperation (op, (args, res))) loc)

    | Input.DefMLType lst ->
       let ctx, lst = mlty_defs ~loc ctx lst in
       (ctx, locate (Syntax.DefMLType lst) loc)

    | Input.DefMLTypeRec lst ->
       let ctx, lst = mlty_rec_defs ~loc ctx lst in
       (ctx, locate (Syntax.DefMLTypeRec lst) loc)

    | Input.DeclConstants (xs, u) ->
       let u = comp ~yield:false ctx u
       and ctx = List.fold_left (fun ctx x -> Ctx.add_constant ~loc x ctx) ctx xs in
       (ctx, locate (Syntax.DeclConstants (xs, u)) loc)

    | Input.TopHandle lst ->
       let lst =
         List.map
           (fun (op, (xs, y, c)) ->
              let k = Ctx.get_operation ~loc op ctx in
              let n = List.length xs in
              if n = k
              then
                let rec fold ctx = function
                  | [] -> ctx
                  | x :: xs ->
                    if not (Name.is_anonymous x) && List.exists (Name.eq_ident x) xs
                    then error ~loc (ParallelShadowing x)
                    else fold (Ctx.add_lexical x ctx) xs
                in
                let ctx = fold ctx xs in
                let ctx = match y with | Some y -> Ctx.add_lexical y ctx | None -> ctx in
                op, (xs, y, comp ~yield:false ctx c)
              else
                error ~loc (ArityMismatch (op, n, k))
           )
           lst
       in
       (ctx, locate (Syntax.TopHandle lst) loc)

    | Input.TopLet lst ->
       let ctx, lst = let_clauses ~loc ~yield:false ctx lst in
       (ctx, locate (Syntax.TopLet lst) loc)

    | Input.TopLetRec lst ->
       let ctx, lst = letrec_clauses ~loc ~yield:false ctx lst in
       (ctx, locate (Syntax.TopLetRec lst) loc)

    | Input.TopDynamic (x, c) ->
       let c = comp ~yield:false ctx c in
       let ctx = Ctx.add_dynamic x ctx in
       (ctx, locate (Syntax.TopDynamic (x, None, c)) loc)

    | Input.TopNow (x, c) ->
       let y = Ctx.get_dynamic ~loc x ctx in
       let c = comp ~yield:false ctx c in
       (ctx, locate (Syntax.TopNow (y, c)) loc)

    | Input.TopDo c ->
       let c = comp ~yield:false ctx c in
       (ctx, locate (Syntax.TopDo c) loc)

    | Input.TopFail c ->
       let c = comp ~yield:false ctx c in
       (ctx, locate (Syntax.TopFail c) loc)

    | Input.Verbosity n ->
       (ctx, locate (Syntax.Verbosity n) loc)

    | Input.Include fs ->
      let rec fold ctx res = function
        | [] -> (ctx, locate (Syntax.Included (List.rev res)) loc)
        | fn::fs ->
          let fn =
            if Filename.is_relative fn
            then Filename.concat basedir fn
            else fn
          in
          if Ctx.included fn ctx
          then
            fold ctx res fs
          else
            let ctx, cmds = file ctx fn in
            fold ctx ((fn, cmds)::res) fs
      in
      fold ctx [] fs

and file ctx fn =
  if Ctx.included fn ctx
  then
    ctx, []
  else
    let basedir = Filename.dirname fn in
    let ctx = Ctx.push_file fn ctx in
    let cmds = Lexer.read_file ?line_limit:None Parser.file fn in
    let ctx, cmds = List.fold_left (fun (ctx,cmds) cmd ->
        let ctx, cmd = toplevel ~basedir ctx cmd in
        (ctx, cmd::cmds))
      (ctx,[]) cmds
    in
    ctx, List.rev cmds

