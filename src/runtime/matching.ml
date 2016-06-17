
let (>>=) = Runtime.bind
let return = Runtime.return

(** Matching *)

exception Match_fail = Runtime.Match_fail
let update = Runtime.match_update


let rec collect_pattern env xvs {Location.thing=p;loc} v =
  match p, v with
  | Syntax.Patt_Anonymous, _ -> xvs

  | Syntax.Patt_As (p,k), v ->
     let xvs = update k v xvs in
     collect_pattern env xvs p v

  | Syntax.Patt_Bound k, v ->
     let v' = Runtime.get_bound ~loc k env in
     if Runtime.equal_value v v'
     then xvs
     else raise Match_fail

  | Syntax.Patt_Jdg p, Runtime.Term j ->
     MatchingTT.collect_jdg_pattern env xvs p j

  | Syntax.Patt_Constructor (tag, ps), Runtime.Tag (tag', vs) when Name.eq_ident tag tag' ->
    multicollect_pattern env xvs ps vs

  | Syntax.Patt_Tuple ps, Runtime.Tuple vs ->
    multicollect_pattern env xvs ps vs

  | Syntax.Patt_Jdg _, (Runtime.Closure _ | Runtime.Handler _ |
                        Runtime.Tag _ | Runtime.Ref _ | Runtime.Tuple _ | Runtime.String _)
  | Syntax.Patt_Constructor _, (Runtime.Term _ | Runtime.Closure _ |
                        Runtime.Handler _ | Runtime.Tag _ | Runtime.Ref _ | Runtime.Tuple _ | Runtime.String _)
  | Syntax.Patt_Tuple _, (Runtime.Term _ | Runtime.Closure _ | Runtime.Handler _ | Runtime.Tag _ | Runtime.Ref _ |
                          Runtime.String _) ->
     raise Match_fail

and multicollect_pattern env xvs ps vs =
  let rec fold xvs = function
    | [], [] -> xvs
    | p::ps, v::vs ->
      let xvs = collect_pattern env xvs p v in
      fold xvs (ps, vs)
    | ([], _::_ | _::_, []) ->
      raise Match_fail
  in
  fold xvs (ps, vs)

let match_pattern p v =
  (* collect values of pattern variables *)
  Runtime.get_env >>= fun env ->
  let r = begin try
    let xvs = collect_pattern env [] p v in
    (* return in decreasing de bruijn order: ready to fold with add_bound *)
    let xvs = List.sort (fun (k,_) (k',_) -> compare k k') xvs in
    let xvs = List.rev_map snd xvs in
    Some xvs
  with Match_fail -> None
  end in
  return r

let match_op_pattern ps pt vs checking =
  Runtime.get_env >>= fun env ->
  let r = begin try
    let xvs = multicollect_pattern env [] ps vs in
    let xvs = match pt with
      | None -> xvs
      | Some p ->
        let v = match checking with
          | Some j -> Predefined.from_option (Some (Runtime.mk_term (Jdg.term_of_ty j)))
          | None -> Predefined.from_option None
       in
       collect_pattern env xvs p v
    in
    (* return in decreasing de bruijn order: ready to fold with add_bound *)
    let xvs = List.sort (fun (k,_) (k',_) -> compare k k') xvs in
    let xvs = List.rev_map snd xvs in
    Some xvs
  with Match_fail -> None
  end in
  return r
