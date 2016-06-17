exception Match_fail = Runtime.Match_fail
let update = Runtime.match_update


let collect_tt_pattern =
  let rec collect env xvs p j =
    let loc = p.Location.loc in
    match p.Location.thing, Jdg.shape j with
    | TT.Syntax.Tt_Anonymous, _ -> xvs

    | TT.Syntax.Tt_As (p,k), _ ->
       let v = Runtime.mk_term j in
       let xvs = update (TT.int_of_bound k) v xvs in
       collect env xvs p j

    | TT.Syntax.Tt_Bound k, _ ->
       let v' = Runtime.get_bound ~loc (TT.int_of_bound k) env in
       if Runtime.equal_value (Runtime.mk_term j) v'
       then xvs
       else raise Match_fail

    | TT.Syntax.Tt_Type, Jdg.Type ->
       xvs

    | TT.Syntax.Tt_Constant x, Jdg.Constant y ->
       if Name.eq_ident x y
       then xvs
       else raise Match_fail

    | TT.Syntax.Tt_Lambda (x,bopt,popt,p), Jdg.Lambda (jy,je) ->
       let xvs = begin match popt with
         | Some pt -> collect env xvs pt (Jdg.term_of_ty (Jdg.atom_ty jy))
         | None -> xvs
       end in
       let yt = Runtime.mk_term (Jdg.atom_term ~loc jy) in
       let env = Runtime.push_bound yt env in
       let xvs = match bopt with
         | None -> xvs
         | Some k -> update (TT.int_of_bound k) yt xvs
       in
       collect env xvs p je

    | TT.Syntax.Tt_Apply (p1,p2), Jdg.Apply (je1,je2) ->
      let xvs = collect env xvs p1 je1 in
      let xvs = collect env xvs p2 je2 in
      xvs

    | TT.Syntax.Tt_Prod (x,bopt,popt,p), Jdg.Prod (jy,jb) ->
       let xvs = begin match popt with
         | Some pt -> collect env xvs pt (Jdg.term_of_ty (Jdg.atom_ty jy))
         | None -> xvs
       end in
       let yt = Runtime.mk_term (Jdg.atom_term ~loc jy) in
       let env = Runtime.push_bound yt env in
       let xvs = match bopt with
         | None -> xvs
         | Some k -> update (TT.int_of_bound k) yt xvs
       in
       collect env xvs p (Jdg.term_of_ty jb)

    | TT.Syntax.Tt_Eq (p1,p2), Jdg.Eq (je1,je2) ->
       let xvs = collect env xvs p1 je1 in
       let xvs = collect env xvs p2 je2 in
       xvs

    | TT.Syntax.Tt_Refl p, Jdg.Refl je ->
       collect env xvs p je

    | TT.Syntax.Tt_GenAtom p, Jdg.Atom x ->
      let j = Jdg.atom_term ~loc x in
      collect env xvs p j

    | TT.Syntax.Tt_GenConstant p, Jdg.Constant c ->
      let signature = Runtime.get_typing_signature env in
      let j = Jdg.form ~loc signature (Jdg.Constant c) in
      collect env xvs p j

    | (TT.Syntax.Tt_Type | TT.Syntax.Tt_Constant _ | TT.Syntax.Tt_Apply _
       | TT.Syntax.Tt_Lambda _ | TT.Syntax.Tt_Prod _
       | TT.Syntax.Tt_Eq _ | TT.Syntax.Tt_Refl _
       | TT.Syntax.Tt_GenAtom _ | TT.Syntax.Tt_GenConstant _) , _ ->
       raise Match_fail

  in
    collect

let collect_jdg_pattern env xvs (pe, pt) j =
   let xvs = collect_tt_pattern env xvs pt (Jdg.term_of_ty (Jdg.typeof j)) in
   collect_tt_pattern env xvs pe j

