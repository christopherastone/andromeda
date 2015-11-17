(** Conversion from sugared to desugared input syntax *)

module IntSet = Set.Make (struct
                    type t = int
                    let compare = compare
                  end)

let add_bound x bound = x :: bound

let rec mk_lambda ys ((c', loc) as c) =
  match ys with
  | [] -> c'
  | _ :: _ ->
    begin match c' with
      | Syntax.Lambda (ys', c) -> mk_lambda (ys @ ys') c
      | _ -> Syntax.Lambda (ys, c)
    end

let rec mk_prod ys ((t', loc) as t) =
  match ys with
  | [] -> t'
  | _ :: _ ->
    begin match t' with
      | Syntax.Prod (ys', t) -> mk_prod (ys @ ys') t
      | _ -> Syntax.Prod (ys, t)
    end

let mk_let ~loc w c =
  match w with
  | [] -> c
  | (_::_) as w -> Syntax.Let (w, c), loc

let rec comp constants bound ((c',loc) as c) =
  (* When a computation [c] is desugared we hoist out a list of
     let-bindings [w]. NB: it is important that we first desugar
     all subexpressions of [c] so that we get the correct environment
     with hoisted bindings, and only then we desugar the subcomputations
     of [c]. *)
  let w, c' = match c' with

    | Input.Operation (op, e) ->
      let w, e = expr constants bound e in
      w, Syntax.Operation (op, e)

    | Input.Handle (c, hcs) ->
       let c = comp constants bound c
       and h = handler ~loc constants bound hcs in
       [], Syntax.With (h, c)

    | Input.With (e, c) ->
       let w, e = expr constants bound e in
       let c = comp constants bound c in
       let c = Syntax.shift_comp (List.length w) 0 c in
       w, Syntax.With (e, c)

    | Input.Let (xcs, c2) ->
      let rec fold = function
        | [] -> []
        | (x,c) :: xcs ->
          if List.mem_assoc x xcs
          then
            Error.syntax ~loc "%t is bound more than once" (Name.print_ident x)
          else
            let c = comp constants bound c in
            let xcs = fold xcs in
            (x, c) :: xcs
      in
      let xcs = fold xcs in
      let bound = List.fold_left (fun bound (x,_) -> add_bound x bound) bound xcs in
      let c2 = comp constants bound c2 in
      [], Syntax.Let (xcs, c2)

    | Input.Assume ((x, t), c) ->
       let t = comp constants bound t in
       let bound = add_bound x bound in
       let c = comp constants bound c in
       [], Syntax.Assume ((x, t), c)

    | Input.Where (c1, e, c2) ->
       let w, e = expr constants bound e
       and c1 = comp constants bound c1
       and c2 = comp constants bound c2 in
       let c1 = Syntax.shift_comp (List.length w) 0 c1
       and c2 = Syntax.shift_comp (List.length w) 0 c2 in
       w, Syntax.Where (c1, e, c2)

    | Input.Match (e, cases) ->
       let w, e = expr constants bound e in
       let bound = List.fold_left (fun bound (x,_) -> add_bound x bound) bound w in
       let cases = List.map (case constants bound) cases in
       w, Syntax.Match (e, cases)

    | Input.Beta (xscs, c) ->
      let xscs = List.map (fun (xs, c) -> xs, comp constants bound c) xscs in
      let c = comp constants bound c in
      [], Syntax.Beta (xscs, c)

    | Input.Eta (xscs, c) ->
      let xscs = List.map (fun (xs, c) -> xs, comp constants bound c) xscs in
      let c = comp constants bound c in
      [], Syntax.Eta (xscs, c)

    | Input.Hint (xscs, c) ->
      let xscs = List.map (fun (xs, c) -> xs, comp constants bound c) xscs in
      let c = comp constants bound c in
      [], Syntax.Hint (xscs, c)

    | Input.Inhabit (xscs, c) ->
      let xscs = List.map (fun (xs, c) -> xs, comp constants bound c) xscs in
      let c = comp constants bound c in
      [], Syntax.Inhabit (xscs, c)

    | Input.Unhint (xs, c) ->
      let c = comp constants bound c in
      [], Syntax.Unhint (xs, c)

    | Input.Ascribe (c, t) ->
       let t = comp constants bound t
       and c = comp constants bound c in
       [], Syntax.Ascribe (c, t)

    | Input.Whnf c ->
      let c = comp constants bound c in
      [], Syntax.Whnf c

    | Input.Typeof c ->
      let c = comp constants bound c in
      [], Syntax.Typeof c

    | Input.Lambda (xs, c) ->
      let rec fold bound ys = function
        | [] ->
           let ys = List.rev ys in
           let c = comp constants bound c in
          mk_lambda ys c
        | (x, None) :: xs ->
          let bound = add_bound x bound
          and ys = (x, None) :: ys in
          fold bound ys xs
        | (x, Some t) :: xs ->
          let ys = (let t = comp constants bound t in (x, Some t) :: ys)
          and bound = add_bound x bound in
          fold bound ys xs
      in
      [], fold bound [] xs

    | Input.Spine (e, cs) ->
      spine constants bound e cs

    | Input.Prod (xs, c) ->
      let rec fold bound ys = function
        | [] ->
           let ys = List.rev ys in
           let c = comp constants bound c in
           mk_prod ys c
        | (x,t) :: xs ->
          let ys = (let t = comp constants bound t in (x, t) :: ys)
          and bound = add_bound x bound in
          fold bound ys xs
      in
      [], fold bound [] xs

    | Input.Eq (c1, c2) ->
      let c1 = comp constants bound c1
      and c2 = comp constants bound c2 in
      [], Syntax.Eq (c1, c2)

    | Input.Refl c ->
      let c = comp constants bound c in
      [], Syntax.Refl c

    | Input.Bracket c ->
      let c = comp constants bound c in
      [], Syntax.Bracket c

    | Input.Inhab ->
      [], Syntax.Inhab

    | Input.Signature lst ->
      let rec fold bound labels res = function
        | [] -> List.rev res
        | (x,y,c)::rem ->
          let y = match y with | Some y -> y | None -> x in
          if List.mem x labels
          then Error.syntax ~loc "field %t appears more than once" (Name.print_ident x)
          else if Name.eq_ident x Name.anonymous
          then Error.syntax ~loc "anonymous field"
          else
            let c = comp constants bound c in
            fold (add_bound y bound) (x::labels) ((x,y,c)::res) rem
        in
      let lst = fold bound [] [] lst in
      [], Syntax.Signature lst

    | Input.Structure lst ->
      let rec fold bound labels res = function
        | [] -> List.rev res
        | (x,y,c) :: rem ->
          let y = match y with | Some y -> y | None -> x in
          if List.mem x labels
          then Error.syntax ~loc "field %t appears more than once" (Name.print_ident x)
          else if Name.eq_ident x Name.anonymous
          then Error.syntax ~loc "anonymous field"
          else
            let c = comp constants bound c in
            fold (add_bound y bound) (x :: labels) ((x,y,c) :: res) rem
        in
      let lst = fold bound [] [] lst in
      [], Syntax.Structure lst

    | Input.Projection (c,x) ->
      let c = comp constants bound c in
      [], Syntax.Projection (c,x)

    | (Input.Var _ | Input.Type | Input.Function _ | Input.Rec _ | Input.Handler _ | Input.Tag _) ->
      let w, e = expr constants bound c in
      w, Syntax.Return e

  in
  mk_let ~loc w (c', loc)

(* Desguar a spine. This function is a bit messy because we need to untangle
   to constants. But it's worth doing to make users happy. *)
and spine constants bound ((e',loc) as e) cs =
  (* Auxiliary function which splits a list into two parts with k
     elements in the first part. *)
  let rec split k lst =
    if k = 0 then
      [], lst
    else
      match lst with
        | [] -> Error.syntax ~loc "this constant needs %d more arguments" k
        | x::lst -> let lst, lst' = split (k-1) lst in (x :: lst, lst')
  in
  (* First we calculate the head of the spine, and the remaining arguments. *)
  let (w, e), cs =
    begin
      match e' with
      | Input.Var x when not (List.mem x bound) ->
        begin
          try
            let k = List.assoc x constants in
            let cs', cs = split k cs in
              (* We make a constant from [x] and [cs'] *)
              constant ~loc constants bound x cs', cs
          with Not_found -> expr constants bound e, cs
        end
      | _ -> expr constants bound e, cs
    end in
  (* Process the remaining arguments. *)
  let k = List.length w in
  let cs = List.map (fun c -> Syntax.shift_comp k 0 (comp constants bound c)) cs in
  w, Syntax.Spine (e, cs)

(* Desugar handler cases. *)
and handler ~loc constants bound hcs =
  let rec fold val_case op_cases finally_case = function
    | [] -> val_case, op_cases, finally_case

    | Input.CaseVal (x, c) :: hcs ->
       begin match val_case with
       | Some _ -> Error.syntax ~loc:(snd c) "value is handled more than once"
       | None ->
          let c = comp constants (add_bound x bound) c in
          fold (Some (x,c)) op_cases finally_case hcs
       end

    | Input.CaseOp (op, x, k, c) :: hcs ->
       if List.mem_assoc op op_cases
       then
         Error.syntax ~loc:(snd c) "operation %s is handled more than once" op
       else
         let bound = add_bound x bound in
         let bound = add_bound k bound in
         let c = comp constants bound c in
         fold val_case ((op, (x, k, c)) :: op_cases) finally_case hcs

    | Input.CaseFinally (x, c) :: hcs ->
       begin match finally_case with
       | Some _ -> Error.syntax ~loc:(snd c) "more than one finally case"
       | None ->
          let c = comp constants (add_bound x bound) c in
          fold val_case op_cases (Some (x,c)) hcs
       end

  in
  let handler_val, handler_ops, handler_finally = fold None [] None hcs in
  Syntax.Handler (Syntax.{handler_val; handler_ops; handler_finally}), loc

(* Desugar a match case *)
and case constants bound (xs, p, c) =
  let rec fold bound = function
    | [] ->
      let varn = List.length xs in
      let p, present = pattern constants bound varn IntSet.empty p in
      let rec check i = function
        | [] -> ()
        | x::xs ->
          if IntSet.mem i present
          then check (i - 1) xs
          else
            Error.syntax ~loc:(snd p) "Match variable %t not present in pattern" (Name.print_ident x)
        in
      check (varn - 1) xs;
      let c = comp constants bound c in
      (xs, p, c)
    | x :: xs ->
      let bound = add_bound x bound in
      fold bound xs
  in
  fold bound xs

(* here be careful as pattern variables are put together with bound variables *)
and pattern constants bound varn present (p,loc) =
  match p with
    | Input.Patt_Anonymous -> (Syntax.Patt_Anonymous, loc), present
    | Input.Patt_As (p,x) ->
      begin match Name.index_of_ident x bound with
        | None ->
          Error.syntax ~loc "%t is not a pattern variable" (Name.print_ident x)
        | Some k ->
          if k < varn
          then
            let present = IntSet.add k present in
            let p, present = pattern constants bound varn present p in
            (Syntax.Patt_As (p,k), loc), present
          else Error.syntax ~loc "%t is not a pattern variable" (Name.print_ident x)
      end
    | Input.Patt_Name x ->
      begin match Name.index_of_ident x bound with
        | None ->
          Error.syntax ~loc "unknown value name %t" (Name.print_ident x)
        | Some k ->
          if k < varn
          then
            let present = IntSet.add k present in
            (Syntax.Patt_As ((Syntax.Patt_Anonymous, loc), k), loc), present
          else
            (Syntax.Patt_Bound (k-varn), loc), present
      end
    | Input.Patt_Jdg (p1,p2) ->
      let p1, present = tt_pattern constants bound varn 0 present p1 in
      let p2, present = tt_pattern constants bound varn 0 present p2 in
      (Syntax.Patt_Jdg (p1,p2), loc), present
    | Input.Patt_Tag (t,ps) ->
      let rec fold present ps = function
        | [] ->
          let ps = List.rev ps in
          (Syntax.Patt_Tag (t,ps), loc), present
        | p::rem ->
          let p, present = pattern constants bound varn present p in
          fold present (p::ps) rem
        in
      fold present [] ps

(* the variables in [bound] are: lvl bound variables, varn pattern variables, then bound variables again *)
and tt_pattern constants bound varn lvl present (p,loc) =
  match p with
    | Input.Tt_Anonymous ->
      (Syntax.Tt_Anonymous, loc), present

    | Input.Tt_As (p,x) ->
      begin match Name.index_of_ident x bound with
        | None ->
          Error.syntax ~loc "%t is not a pattern variable" (Name.print_ident x)
        | Some k ->
          if k < lvl
          then Error.syntax ~loc "%t is not a pattern variable" (Name.print_ident x)
          else if k-lvl < varn
          then
            let present = IntSet.add (k-lvl) present in
            let p, present = tt_pattern constants bound varn lvl present p in
            (Syntax.Tt_As (p,k), loc), present
          else Error.syntax ~loc "%t is not a pattern variable" (Name.print_ident x)
      end

    | Input.Tt_Type ->
      (Syntax.Tt_Type, loc), present

    | Input.Tt_Name x ->
      begin match Name.index_of_ident x bound with
        | None ->
          if List.mem_assoc x constants
          then
            (Syntax.Tt_Constant x, loc), present
          else
            Error.syntax ~loc "unknown name %t" (Name.print_ident x)
        | Some k ->
          if k < lvl
          then (Syntax.Tt_Bound k, loc), present
          else if k-lvl < varn
          then
            let present = IntSet.add (k-lvl) present in
            (Syntax.Tt_As ((Syntax.Tt_Anonymous, loc), k-lvl), loc), present
          else
            (Syntax.Tt_Bound (k-varn), loc), present
      end

    | Input.Tt_Lambda (x,popt,p) ->
      let popt, present = match popt with
        | None ->
          None, present
        | Some p ->
          let p,present = tt_pattern constants bound varn lvl present p in
          Some p, present
        in
      let bopt, present = match Name.index_of_ident x bound with
        | None -> None, present
        | Some k ->
          if k >= lvl && k-lvl < varn
          then Some (k-lvl), IntSet.add (k-lvl) present
          else None, present
        in
      let p, present = tt_pattern constants (add_bound x bound) varn (lvl+1) present p in
      (Syntax.Tt_Lambda (x,bopt,popt,p), loc), present

    | Input.Tt_App (p1,p2) ->
      let p1, present = tt_pattern constants bound varn lvl present p1 in
      let p2, present = tt_pattern constants bound varn lvl present p2 in
      (Syntax.Tt_App (p1,p2), loc), present

    | Input.Tt_Prod (x,popt,p) ->
      let popt, present = match popt with
        | None ->
          None, present
        | Some p ->
          let p,present = tt_pattern constants bound varn lvl present p in
          Some p, present
        in
      let bopt, present = match Name.index_of_ident x bound with
        | None -> None, present
        | Some k ->
          if k >= lvl && k-lvl < varn
          then Some (k-lvl), IntSet.add (k-lvl) present
          else None, present
        in
      let p, present = tt_pattern constants (add_bound x bound) varn (lvl+1) present p in
      (Syntax.Tt_Prod (x,bopt,popt,p), loc), present

    | Input.Tt_Eq (p1,p2) ->
      let p1, present = tt_pattern constants bound varn lvl present p1 in
      let p2, present = tt_pattern constants bound varn lvl present p2 in
      (Syntax.Tt_Eq (p1,p2), loc), present

    | Input.Tt_Refl p ->
      let p, present = tt_pattern constants bound varn lvl present p in
      (Syntax.Tt_Refl p, loc), present

    | Input.Tt_Inhab ->
      (Syntax.Tt_Inhab, loc), present

    | Input.Tt_Bracket p ->
      let p, present = tt_pattern constants bound varn lvl present p in
      (Syntax.Tt_Bracket p, loc), present

    | Input.Tt_Signature xps ->
      let rec fold bound lvl present xps = function
        | [] ->
          let xps = List.rev xps in
          (Syntax.Tt_Signature xps, loc), present
        | (l,xopt,p)::rem ->
          let x = match xopt with | Some x -> x | None -> l in
          let bopt, present = match Name.index_of_ident x bound with
            | None -> None, present
            | Some k ->
              if k >= lvl && k-lvl < varn
              then Some (k-lvl), IntSet.add (k-lvl) present
              else None, present
            in
          let p, present = tt_pattern constants bound varn lvl present p in
          fold (add_bound x bound) (lvl+1) present ((l,x,bopt,p)::xps) rem
        in
      fold bound lvl present [] xps

    | Input.Tt_Structure xps ->
      let rec fold bound lvl present xps = function
        | [] ->
          let xps = List.rev xps in
          (Syntax.Tt_Structure xps, loc), present
        | (l,xopt,p)::rem ->
          let x = match xopt with | Some x -> x | None -> l in
          let bopt, present = match Name.index_of_ident x bound with
            | None -> None, present
            | Some k ->
              if k >= lvl && k-lvl < varn
              then Some (k-lvl), IntSet.add (k-lvl) present
              else None, present
            in
          let p, present = tt_pattern constants bound varn lvl present p in
          fold (add_bound x bound) (lvl+1) present ((l,x,bopt,p)::xps) rem
        in
      fold bound lvl present [] xps

    | Input.Tt_Projection (p,l) ->
      let p, present = tt_pattern constants bound varn lvl present p in
      (Syntax.Tt_Projection (p,l), loc), present

(* Make constant as if it were in an expression position *)
and constant ~loc constants bound x cs =
  let cs = List.map (comp constants bound) cs in
  let c = Syntax.Constant (x, cs), loc
  and y = Name.fresh_candy () in
  [(y, c)], (Syntax.Bound 0, loc)

(* Desugar an expression. It hoists out subcomputations appearing in the
   expression. *)
and expr constants bound ((e', loc) as e) =
  match e' with
  | Input.Var x ->
    begin
      (* a bound variable always shadows a name *)
      match Name.index_of_ident x bound with
      | None ->
        (* it is a constants operation of arity 0 *)
        begin
          try
            let k = List.assoc x constants in
            if k = 0 then constant ~loc constants bound x []
            else Error.syntax ~loc "this constant needs %d more arguments" k
          with Not_found ->
            Error.syntax ~loc "unknown name %t" (Name.print_ident x)
        end
      | Some k -> [], (Syntax.Bound k, loc)
    end

  | Input.Type ->
    [], (Syntax.Type, loc)

  | Input.Function (xs, c) ->
     let rec fold bound = function
       | [] -> Error.impossible ~loc "empty function abstraction in desugar"
       | [x] ->
          let bound = add_bound x bound in
          let c = comp constants bound c in
            Syntax.Function (x, c), loc
       | x :: ((_ :: _) as xs) ->
          let bound = add_bound x bound in
          let e = fold bound xs in
            Syntax.Function (x, (Syntax.Return e, loc)), loc
     in
       [], fold bound xs

  | Input.Rec (f, xs, c) ->
     let rec fold bound = function
       | [] -> comp constants bound c
       | y :: ys ->
          let bound = add_bound y bound in
          let c = fold bound ys in
            Syntax.Return (Syntax.Function (y, c), loc), loc
     in
     begin match xs with
     | [] -> Error.impossible ~loc "empty recursion abstraction in desguar"
     | x :: xs ->
        let bound = add_bound f bound in
        let bound = add_bound x bound in
        let c = fold bound xs in
        [], (Syntax.Rec (f, x, c), loc)
     end

  | Input.Handler hcs ->
     [], handler ~loc constants bound hcs

  | Input.Tag (t, lst) ->
     let rec fold w es bound = function
       | [] ->
          let es = List.rev es in
          w, es
       | c :: cs ->
          let we, e = expr constants bound c in
          let bound = List.fold_left (fun bound (x, _) -> add_bound x bound) bound we in
          fold (w @ we) (e :: es) bound cs
     in
     let w, es = fold [] [] bound lst in
     w, (Syntax.Tag (t, es), loc)

  | (Input.Let _ | Input.Beta _ | Input.Eta _ | Input.Hint _ | Input.Inhabit _ |
     Input.Unhint _ | Input.Bracket _ | Input.Inhab | Input.Ascribe _ | Input.Lambda _ |
     Input.Spine _ | Input.Prod _ | Input.Eq _ | Input.Refl _ | Input.Operation _ |
     Input.Whnf _ | Input.Match _ | Input.Handle _ | Input.With _ |
     Input.Typeof _ | Input.Assume _ | Input.Where _ | Input.Signature _ |
     Input.Structure _ | Input.Projection _) ->
    let x = Name.fresh_candy ()
    and c = comp constants bound e in
    [(x,c)], (Syntax.Bound 0, loc)

let toplevel constants bound (d', loc) =
  let d' = match d' with

    | Input.Axiom (x, ryts, u) ->
      let rec fold bound ryts' = function
        | [] ->
          let u = comp constants bound u in
          let ryts' = List.rev ryts' in
          (ryts', u)
        | (reducing, (y, t)) :: ryts ->
          let t = comp constants bound t in
          let bound = add_bound y bound
          and ryts' = (reducing, (y, t)) :: ryts' in
          fold bound ryts' ryts
      in
      let ryts, u = fold bound [] ryts in
      Syntax.Axiom (x, ryts, u)

    | Input.TopLet (x, yts, u, ((_, loc) as c)) ->
      let c = match u with
        | None -> c
        | Some u ->
          Input.Ascribe (c, u), loc in
      let yts = List.map (fun (y, t) -> y, Some t) yts in
      let c = Input.Lambda (yts, c), loc in
      let c = comp constants bound c in
      Syntax.TopLet (x, c)

    | Input.TopCheck c ->
      let c = comp constants bound c in
      Syntax.TopCheck c

    | Input.TopBeta xscs ->
      let xscs = List.map (fun (xs, c) -> xs, comp constants bound c) xscs in
      Syntax.TopBeta xscs

    | Input.TopEta xscs ->
      let xscs = List.map (fun (xs, c) -> xs, comp constants bound c) xscs in
      Syntax.TopEta xscs

    | Input.TopHint xscs ->
      let xscs = List.map (fun (xs, c) -> xs, comp constants bound c) xscs in
      Syntax.TopHint xscs

    | Input.TopInhabit xscs ->
      let xscs = List.map (fun (xs, c) -> xs, comp constants bound c) xscs in
      Syntax.TopInhabit xscs

    | Input.TopUnhint xs -> Syntax.TopUnhint xs

    | Input.Quit -> Syntax.Quit

    | Input.Help -> Syntax.Help

    | Input.Verbosity n -> Syntax.Verbosity n

    | Input.Include fs -> Syntax.Include fs

    | Input.Environment -> Syntax.Environment

  in
  d', loc
