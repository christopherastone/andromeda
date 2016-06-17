
let (>>=) = Tyenv.(>>=)

(* tt_pattern : ('a * Mlty.ty) list -> TT.Syntax.tt_pattern -> unit Tyenv.tyenv *)
let rec tt_pattern xs {Location.thing = p; loc} =
  match p with
  | TT.Syntax.Tt_Anonymous -> Tyenv.return ()

  | TT.Syntax.Tt_As (p, k) ->
    let _, t = List.nth xs (TT.int_of_bound k) in
    Tyenv.add_equation ~loc t Mlty.Jdg >>= fun () ->
    tt_pattern xs p

  | TT.Syntax.Tt_Bound k ->
    Tyenv.lookup_var (TT.int_of_bound k) >>= fun t ->
    Tyenv.add_equation ~loc t Mlty.Jdg

  | TT.Syntax.Tt_Type -> Tyenv.return ()

  | TT.Syntax.Tt_Constant _ -> Tyenv.return ()

  | TT.Syntax.Tt_Lambda (x, _, popt, p)
  | TT.Syntax.Tt_Prod (x, _, popt, p) ->
    begin match popt with
      | Some pt -> tt_pattern xs pt
      | None -> Tyenv.return ()
    end >>= fun () ->
    Tyenv.add_var x Mlty.Jdg (tt_pattern xs p)

  | TT.Syntax.Tt_Apply (p1, p2)
  | TT.Syntax.Tt_Eq (p1, p2) ->
    tt_pattern xs p1 >>= fun () ->
    tt_pattern xs p2

  | TT.Syntax.Tt_Refl p | TT.Syntax.Tt_GenAtom p | TT.Syntax.Tt_GenConstant p ->
    tt_pattern xs p

let tt_jdg xs (p1,p2) =
    tt_pattern xs p1 >>= fun () ->
    tt_pattern xs p2 >>= fun () ->
    Tyenv.return Mlty.Jdg




let locate ~loc v = Location.locate v loc

let compTT ~loc (check_comp) ttc : (Mlty.ty_schema Syntax.comp * Mlty.ty) Tyenv.tyenvM =
  let wrap ttc' = locate ~loc (Syntax.TTc ttc') in
  match ttc with
    | TT.Syntax.Type ->
      Tyenv.return (wrap TT.Syntax.Type, Mlty.Jdg)

    | TT.Syntax.Constant c ->
      Tyenv.return (wrap (TT.Syntax.Constant c), Mlty.Jdg)

    | TT.Syntax.Lambda (x, copt, c) ->
      begin match copt with
        | Some ct -> check_comp ct Mlty.Jdg >>= fun ct -> Tyenv.return (Some ct)
        | None -> Tyenv.return None
      end >>= fun copt ->
      Tyenv.add_var x Mlty.Jdg (check_comp c Mlty.Jdg) >>= fun c ->
      Tyenv.return (wrap (TT.Syntax.Lambda (x, copt, c)), Mlty.Jdg)

    | TT.Syntax.Prod (x, ct, c) ->
      check_comp ct Mlty.Jdg >>= fun ct ->
      Tyenv.add_var x Mlty.Jdg (check_comp c Mlty.Jdg) >>= fun c ->
      Tyenv.return (wrap (TT.Syntax.Prod (x, ct, c)), Mlty.Jdg)

    | TT.Syntax.Eq (c1, c2) ->
      check_comp c1 Mlty.Jdg >>= fun c1 ->
      check_comp c2 Mlty.Jdg >>= fun c2 ->
      Tyenv.return (wrap (TT.Syntax.Eq (c1, c2)), Mlty.Jdg)

    | TT.Syntax.Refl c ->
      check_comp c Mlty.Jdg >>= fun c ->
      Tyenv.return (wrap (TT.Syntax.Refl c), Mlty.Jdg)

    | TT.Syntax.CongrProd (c1, c2, c3) ->
      check_comp c1 Mlty.Jdg >>= fun c1 ->
      check_comp c2 Mlty.Jdg >>= fun c2 ->
      check_comp c3 Mlty.Jdg >>= fun c3 ->
      Tyenv.return (wrap (TT.Syntax.CongrProd (c1, c2, c3)), Mlty.Jdg)

    | TT.Syntax.CongrApply (c1, c2, c3, c4, c5) ->
      check_comp c1 Mlty.Jdg >>= fun c1 ->
      check_comp c2 Mlty.Jdg >>= fun c2 ->
      check_comp c3 Mlty.Jdg >>= fun c3 ->
      check_comp c4 Mlty.Jdg >>= fun c4 ->
      check_comp c5 Mlty.Jdg >>= fun c5 ->
      Tyenv.return (wrap (TT.Syntax.CongrApply (c1, c2, c3, c4, c5)), Mlty.Jdg)

    | TT.Syntax.CongrLambda (c1, c2, c3, c4) ->
      check_comp c1 Mlty.Jdg >>= fun c1 ->
      check_comp c2 Mlty.Jdg >>= fun c2 ->
      check_comp c3 Mlty.Jdg >>= fun c3 ->
      check_comp c4 Mlty.Jdg >>= fun c4 ->
      Tyenv.return (wrap (TT.Syntax.CongrLambda (c1, c2, c3, c4)), Mlty.Jdg)

    | TT.Syntax.CongrEq (c1, c2, c3) ->
      check_comp c1 Mlty.Jdg >>= fun c1 ->
      check_comp c2 Mlty.Jdg >>= fun c2 ->
      check_comp c3 Mlty.Jdg >>= fun c3 ->
      Tyenv.return (wrap (TT.Syntax.CongrEq (c1, c2, c3)), Mlty.Jdg)

    | TT.Syntax.CongrRefl (c1, c2) ->
      check_comp c1 Mlty.Jdg >>= fun c1 ->
      check_comp c2 Mlty.Jdg >>= fun c2 ->
      Tyenv.return (wrap (TT.Syntax.CongrRefl (c1, c2)), Mlty.Jdg)

    | TT.Syntax.BetaStep (c1, c2, c3, c4, c5) ->
      check_comp c1 Mlty.Jdg >>= fun c1 ->
      check_comp c2 Mlty.Jdg >>= fun c2 ->
      check_comp c3 Mlty.Jdg >>= fun c3 ->
      check_comp c4 Mlty.Jdg >>= fun c4 ->
      check_comp c5 Mlty.Jdg >>= fun c5 ->
      Tyenv.return (wrap (TT.Syntax.BetaStep (c1, c2, c3, c4, c5)), Mlty.Jdg)


