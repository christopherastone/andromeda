(** Evaluation of computations *)

(** Notation for the monadic bind *)
let (>>=) = Runtime.bind

(** A computation filter that verifies the result is a term,
    and fails otherwise. *)
let as_term = EvalTT.as_term


(** Returns the atom with its natural type in [ctx] *)
(* as_atom: loc:Location.t -> Runtime.value -> Jdg.term Runtime.comp *)
let as_atom = EvalTT.as_atom

(* as_handler: loc:Location.t -> Runtime.value -> Runtime.handler Runtime.comp *)
let as_handler ~loc v =
  let e = Runtime.as_handler ~loc v in
  Runtime.return e

(* as_ref: loc:Location.t -> Runtime.value -> Runtime.ref Runtime.comp *)
let as_ref ~loc v =
  let e = Runtime.as_ref ~loc v in
  Runtime.return e


(** Evaluate a computation -- infer mode. *)
(*   infer : 'annot Syntax.comp -> Runtime.value Runtime.comp *)
let rec infer {Location.thing=c'; loc} =
  match c' with
    | Syntax.Bound i ->
       Runtime.lookup_bound ~loc i

    | Syntax.TTc ttc ->
       EvalTT.inferTT ~loc (check, check_ty, infer) ttc

    | Syntax.Function (_, c) ->
       let f v =
         Runtime.add_bound v
           (infer c)
       in
       Runtime.return_closure f

    | Syntax.Constructor (t, cs) ->
       let rec fold vs = function
         | [] ->
            let vs = List.rev vs in
            let v = Runtime.mk_tag t vs in
            Runtime.return v
         | c :: cs ->
            infer c >>= fun v ->
            fold (v :: vs) cs
       in
       fold [] cs

    | Syntax.Tuple cs ->
      let rec fold vs = function
        | [] -> Runtime.return (Runtime.mk_tuple (List.rev vs))
        | c :: cs -> (infer c >>= fun v -> fold (v :: vs) cs)
      in
      fold [] cs

    | Syntax.Handler {Syntax.handler_val; handler_ops; handler_finally} ->
        let handler_val =
          begin match handler_val with
          | [] -> None
          | _ :: _ ->
            let f v =
              match_cases ~loc handler_val infer v
            in
            Some f
          end
        and handler_ops = Name.IdentMap.mapi (fun op cases ->
            let f {Runtime.args=vs;checking} =
              match_op_cases ~loc op cases vs checking
            in
            f)
          handler_ops
        and handler_finally =
          begin match handler_finally with
          | [] -> None
          | _ :: _ ->
            let f v =
              match_cases ~loc handler_finally infer v
            in
            Some f
          end
        in
        Runtime.return_handler handler_val handler_ops handler_finally

  | Syntax.Operation (op, cs) ->
     let rec fold vs = function
       | [] ->
          let vs = List.rev vs in
          Runtime.operation op vs
       | c :: cs ->
          infer c >>= fun v ->
          fold (v :: vs) cs
     in
     fold [] cs

  | Syntax.With (c1, c2) ->
     infer c1 >>= as_handler ~loc >>= fun h ->
     Runtime.handle_comp h (infer c2)

  | Syntax.Let (xcs, c) ->
     let_bind xcs (infer c)

  | Syntax.LetRec (fxcs, c) ->
     letrec_bind fxcs (infer c)

  | Syntax.Now (x,c1,c2) ->
    infer c1 >>= fun v ->
    Runtime.now ~loc x v (infer c2)

  | Syntax.Ref c ->
     infer c >>= fun v ->
     Runtime.mk_ref v

  | Syntax.Lookup c ->
     infer c >>= as_ref ~loc >>= fun x ->
     Runtime.lookup_ref x

  | Syntax.Update (c1, c2) ->
     infer c1 >>= as_ref ~loc >>= fun x ->
     infer c2 >>= fun v ->
     Runtime.update_ref x v >>= fun () ->
     Runtime.return_unit

  | Syntax.Sequence (c1, c2) ->
     infer c1 >>= fun v ->
     sequence ~loc v >>= fun () ->
     infer c2

  | Syntax.Assume ((x, t), c) ->
     check_ty t >>= fun t ->
     Runtime.add_free ~loc x t (fun _ ->
       infer c)

  | Syntax.Where (c1, c2, c3) ->
    infer c2 >>= as_atom ~loc >>= fun a ->
    infer c1 >>= as_term ~loc:(c1.Location.loc) >>= fun je ->
    begin match Jdg.occurs a je with
    | None ->
       check c3 (Jdg.atom_ty a) >>= fun _ ->
       Runtime.return_term je
    | Some a ->
       check c3 (Jdg.atom_ty a) >>= fun js ->
       let j = Jdg.substitute ~loc je a js in
       Runtime.return_term j
    end

  | Syntax.Match (c, cases) ->
     infer c >>=
     match_cases ~loc cases infer

  | Syntax.External s ->
     begin match External.lookup s with
       | None -> Runtime.(error ~loc (UnknownExternal s))
       | Some v -> v loc
     end

  | Syntax.Ascribe (c1, c2) ->
     check_ty c2 >>= fun t ->
     check c1 t >>=
     Runtime.return_term


  | Syntax.Apply (c1, c2) ->
    infer c1 >>= begin function
      | Runtime.Term j ->
        EvalTT.apply ~loc (check, check_ty, infer) j c2
      | Runtime.Closure f ->
        infer c2 >>= fun v ->
        Runtime.apply_closure f v
      | Runtime.Handler _ | Runtime.Tag _ | Runtime.Tuple _ |
        Runtime.Ref _ | Runtime.String _ as h ->
        Runtime.(error ~loc (Inapplicable h))
    end


  | Syntax.Yield c ->
    infer c >>= fun v ->
    Runtime.continue ~loc v

  | Syntax.String s ->
    Runtime.return (Runtime.mk_string s)

  | Syntax.Occurs (c1,c2) ->
    infer c1 >>= as_atom ~loc >>= fun a ->
    infer c2 >>= as_term ~loc >>= fun j ->
    begin match Jdg.occurs a j with
      | Some jx ->
        let j = Jdg.term_of_ty (Jdg.atom_ty jx) in
        Runtime.return (Predefined.from_option (Some (Runtime.mk_term j)))
      | None ->
        Runtime.return (Predefined.from_option None)
    end

  | Syntax.Context c ->
    infer c >>= as_term ~loc >>= fun j ->
    let ctx = Jdg.contextof j in
    let xts = Jdg.Ctx.elements ctx in
    let js = List.map (fun j -> Runtime.mk_term (Jdg.atom_term ~loc j)) xts in
    Runtime.return (Predefined.mk_list js)

  | Syntax.Natural c ->
    infer c >>= as_term ~loc >>= fun j ->
    Runtime.lookup_typing_signature >>= fun signature ->
    let eq = Jdg.natural_eq ~loc signature j in
    let e = Jdg.refl_of_eq_ty ~loc eq in
    Runtime.return_term e

and check_default_v ~loc v t_check =
  as_term ~loc v >>= fun je ->
  Equal.coerce ~loc je t_check >>=
    begin function
      | Some je -> Runtime.return je
      | None -> Jdg.errorTypeMismatchCheckingMode ~loc je t_check
  end

and check_default ~loc c t_check =
  infer c >>= fun v ->
  check_default_v ~loc v t_check

(* 'annot Syntax.comp -> Jdg.ty -> Jdg.term Runtime.comp *)
and check ({Location.thing=c';loc} as c) t_check =
  match c' with
  | Syntax.Bound _
  | Syntax.Function _
  | Syntax.Handler _
  | Syntax.Ascribe _
  | Syntax.External _
  | Syntax.Constructor _
  | Syntax.Tuple _
  | Syntax.Where _
  | Syntax.With _
  | Syntax.Apply _
  | Syntax.Yield _
  | Syntax.Ref _
  | Syntax.Lookup _
  | Syntax.Update _
  | Syntax.String _
  | Syntax.Occurs _
  | Syntax.Context _
  | Syntax.Natural _ ->
    (** this is the [check-infer] rule, which applies for all term formers "foo"
        that don't have a "check-foo" rule *)

    check_default ~loc c t_check

  | Syntax.Operation (op, cs) ->
     let rec fold vs = function
       | [] ->
          let vs = List.rev vs in
          Runtime.operation op ~checking:t_check vs >>= fun v ->
          check_default_v ~loc v t_check
       | c :: cs ->
          infer c >>= fun v ->
          fold (v :: vs) cs
     in
     fold [] cs

  | Syntax.Let (xcs, c) ->
     let_bind xcs (check c t_check)

  | Syntax.Sequence (c1,c2) ->
    infer c1 >>= fun v ->
    sequence ~loc v >>= fun () ->
    check c2 t_check

  | Syntax.LetRec (fxcs, c) ->
     letrec_bind fxcs (check c t_check)

  | Syntax.Now (x,c1,c2) ->
    infer c1 >>= fun v ->
    Runtime.now ~loc x v (check c2 t_check)

  | Syntax.Assume ((x, t), c) ->
     check_ty t >>= fun t ->
     Runtime.add_free ~loc x t (fun _ ->
     check c t_check)

  | Syntax.Match (c, cases) ->
     infer c >>=
     match_cases ~loc cases (fun c -> check c t_check)

  | Syntax.TTc ttc ->
      EvalTT.checkTT ~loc (check, check_ty, infer) ttc t_check



(* sequence: loc:Location.t -> Runtime.value -> unit Runtime.comp *)
and sequence ~loc v =
  match v with
    | Runtime.Tuple [] -> Runtime.return ()
    | _ ->
      Runtime.lookup_penv >>= fun penv ->
      Print.warning "%t: Sequence:@ The value %t should be ()" (Location.print loc) (Runtime.print_value ~penv v);
      Runtime.return ()

and let_bind : 'a. _ -> 'a Runtime.comp -> 'a Runtime.comp = fun xcs cmd ->
  let rec fold vs = function
    | [] ->
      (* parallel let: only bind at the end *)
      List.fold_left  (fun cmd v -> Runtime.add_bound v cmd) cmd vs
    | (_, _, c) :: xcs ->
      infer c >>= fun v ->
      fold (v :: vs) xcs
    in
  fold [] xcs

and letrec_bind : 'a. _ -> 'a Runtime.comp -> 'a Runtime.comp = fun fxcs ->
  let gs =
    List.map
      (fun (_, _, _, c) -> (fun v -> Runtime.add_bound v (infer c)))
      fxcs
  in
  Runtime.add_bound_rec gs

(* [match_cases loc cases eval v] tries for each case in [cases] to match [v]
   and if successful continues on the computation using [eval] with the pattern variables bound. *)
and match_cases : type a. loc:_ -> _ -> ('annot Syntax.comp -> a Runtime.comp) -> _ -> a Runtime.comp
 = fun ~loc cases eval v ->
  let rec fold = function
    | [] ->
      Runtime.lookup_penv >>= fun penv ->
      Runtime.(error ~loc (MatchFail v))
    | (xs, p, c) :: cases ->
      Matching.match_pattern p v >>= begin function
        | Some vs ->
          let rec bind = function
            | [] -> eval c
            | v::vs ->
              Runtime.add_bound v (bind vs)
          in
          bind vs
        | None -> fold cases
      end
  in
  fold cases

and match_op_cases ~loc op cases vs checking =
  let rec fold = function
    | [] ->
      Runtime.operation op ?checking vs >>= fun v ->
      Runtime.continue ~loc v
    | (xs, ps, pt, c) :: cases ->
      Matching.match_op_pattern ps pt vs checking >>= begin function
        | Some vs ->
          let rec bind = function
            | [] -> infer c
            | v::vs ->
              Runtime.add_bound v (bind vs)
          in
          bind vs
        | None -> fold cases
      end
  in
  fold cases

and check_ty c : Jdg.ty Runtime.comp =
  check c Jdg.ty_ty >>= fun j ->
  Runtime.return (Jdg.is_ty ~loc:c.Location.loc j)


(** Move to toplevel monad *)

(* comp_value: 'a Syntax.comp -> Runtime.value Runtime.toplevel *)
let comp_value c =
  let r = infer c in
  Runtime.top_handle ~loc:c.Location.loc r

(* comp_ty: 'a Syntax.comp -> Jdg.ty Runtime.toplevel *)
let comp_ty c =
  let r = check_ty c in
  Runtime.top_handle ~loc:(c.Location.loc) r

let comp_handle (xs,y,c) =
  Runtime.top_return_closure (fun (vs,checking) ->
      let rec bind = function
        | [] ->
           begin match y with
           | Some _ ->
              let checking = match checking with
                | Some jt -> Some (Runtime.mk_term (Jdg.term_of_ty jt))
                | None -> None
              in
              let vy = Predefined.from_option checking in
              Runtime.add_bound vy (infer c)
           | None -> infer c
           end
        | v::vs -> Runtime.add_bound v (bind vs)
      in
      bind vs)

(** Toplevel commands *)

let (>>=) = Runtime.top_bind
let return = Runtime.top_return

let toplet_bind ~loc ~quiet ~print_annot xcs =
  let rec fold xvs = function
    | [] ->
       (* parallel let: only bind at the end *)
       List.fold_left
         (fun cmd (x, v) -> Runtime.add_topbound v >>= fun () -> cmd)
         (return ())
         xvs
    | (x, s, c) :: xcs ->
       comp_value c >>= fun v ->
       fold ((x, v) :: xvs) xcs
  in
  fold [] xcs >>= fun () ->
  begin if not quiet then
    Format.printf "%t@." (Print.sequence
      (fun (x, annot, _) ppf -> Format.fprintf ppf "@[<hov 2>val %t :@ %t@]@." (Name.print_ident x) (print_annot annot))
      ""
      xcs)
  end;
  return ()

let topletrec_bind ~loc ~quiet ~print_annot fxcs =
  let gs =
    List.map
      (fun (_, _, _, c) -> (fun v -> Runtime.add_bound v (infer c)))
      fxcs
  in
  Runtime.add_topbound_rec gs >>= fun () ->
  begin if not quiet then
    Format.printf "%t@." (Print.sequence
      (fun (f, _, annot, _) ppf -> Format.fprintf ppf "@[<hov 2>val %t :@ %t@]@." (Name.print_ident f) (print_annot annot))
      ""
      fxcs)
  end;
  return ()

type error =
  | RuntimeError of TT.print_env * Runtime.error
  | JdgError of TT.print_env * Jdg.error

exception Error of error Location.located

let error ~loc err = Pervasives.raise (Error (Location.locate err loc))

let print_error err ppf =
  match err with
    | RuntimeError (penv, err) -> Runtime.print_error ~penv err ppf
    | JdgError (penv, err) -> Jdg.print_error ~penv err ppf

let rec toplevel ~quiet ~print_annot {Location.thing=c;loc} =
  Runtime.catch (lazy (match c with

    | Syntax.DefMLType lst
    | Syntax.DefMLTypeRec lst ->
      (if not quiet then Format.printf "ML type%s %t declared.@.@." (match lst with [_] -> "" | _ -> "s") (Print.sequence (fun (t,_) -> Name.print_ident t) " " lst));
      return ()

    | Syntax.DeclOperation (x, k) ->
       if not quiet then Format.printf "Operation %t is declared.@.@." (Name.print_ident x) ;
       return ()

    | Syntax.DeclConstants (xs, c) ->
      comp_ty c >>= fun t ->
      let t = Jdg.is_closed_ty ~loc t in
      let rec fold = function
        | [] -> (if not quiet then Format.printf "@."); return ()
        | x :: xs ->
          Runtime.add_constant ~loc x t >>= fun () ->
          (if not quiet then Format.printf "Constant %t is declared.@." (Name.print_ident x) ;
           fold xs)
      in
      fold xs

    | Syntax.TopHandle lst ->
       Runtime.top_fold (fun () (op, xc) ->
           comp_handle xc >>= fun f ->
           Runtime.add_handle op f) () lst

    | Syntax.TopLet xcs ->
      let print_annot = print_annot () in
      toplet_bind ~loc ~quiet ~print_annot xcs

    | Syntax.TopLetRec fxcs ->
      let print_annot = print_annot () in
      topletrec_bind ~loc ~quiet ~print_annot fxcs

    | Syntax.TopDynamic (x, annot, c) ->
       comp_value c >>= fun v ->
       Runtime.add_dynamic ~loc x v

    | Syntax.TopNow (x,c) ->
       comp_value c >>= fun v ->
       Runtime.top_now ~loc x v

    | Syntax.TopDo c ->
       comp_value c >>= fun v ->
       Runtime.top_lookup_penv >>= fun penv ->
       (begin if not quiet then
            Format.printf "%t@.@." (Runtime.print_value ~penv v)
        end;
        return ())

    | Syntax.TopFail c ->
       Runtime.catch (lazy (comp_value c)) >>= begin function

       | Runtime.CaughtRuntime {Location.thing=err; loc}  ->
         Runtime.top_lookup_penv >>= fun penv ->
         (if not quiet then Format.printf "Successfully failed command with runtime error:@.%t:@ %t@.@."
                                          (Location.print loc)
                                          (Runtime.print_error ~penv err));
         return ()

       | Runtime.CaughtJdg {Location.thing=err; loc}  ->
         Runtime.top_lookup_penv >>= fun penv ->
         (if not quiet then Format.printf "Successfully failed command with judgment error:@.%t:@ %t@.@."
                                          (Location.print loc)
                                          (Jdg.print_error ~penv err));
         return ()

       | Runtime.Value v ->
         Runtime.error ~loc (Runtime.FailureFail v)
       end

    | Syntax.Included lst ->
      Runtime.top_fold (fun () (fn, cmds) ->
          (if not quiet then Format.printf "#including %s@." fn);
          Runtime.top_fold (fun () cmd -> toplevel ~quiet:true ~print_annot cmd) () cmds >>= fun () ->
          (if not quiet then Format.printf "#processed %s@." fn);
          return ())
        () lst

    | Syntax.Verbosity i -> Config.verbosity := i; return ()
  )) >>= function
  | Runtime.CaughtJdg {Location.thing=err; loc}  ->
    Runtime.top_lookup_penv >>= fun penv ->
    error ~loc (JdgError (penv, err))

  | Runtime.CaughtRuntime {Location.thing=err; loc}  ->
    Runtime.top_lookup_penv >>= fun penv ->
    error ~loc (RuntimeError (penv, err))

  | Runtime.Value v -> return v
