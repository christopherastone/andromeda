let ( >>= ) = Runtime.bind

(** Form a judgement *)
(* loc:Location.t -> Jdg.shape -> Jdg.term Runtime.comp *)
let jdg_form ~loc s =
  Runtime.lookup_typing_signature >>= fun signature ->
  Runtime.return (Jdg.form ~loc signature s)

(** A computation filter that verifies the result is a term,
    and fails otherwise. *)
(* as_term : loc:Location.t -> Runtime.value -> Jdg.term Runtime.comp *)
let as_term ~loc v =
  let e = Runtime.as_term ~loc v in
    Runtime.return e

(** Returns the atom with its natural type in [ctx] *)
(* as_atom: loc:Location.t -> Runtime.value -> Jdg.term Runtime.comp *)
let as_atom ~loc v =
  as_term ~loc v >>= fun j ->
  match Jdg.shape j with
    | Jdg.Atom x -> Runtime.return x
    | _ -> Jdg.errorExpectedAtom ~loc j

let inferTT ~loc (check,check_ty,infer) ttc =
  match ttc with
    | TT.Syntax.Type ->
      jdg_form ~loc Jdg.Type >>=
      Runtime.return_term

    | TT.Syntax.Constant x ->
      jdg_form ~loc (Jdg.Constant x) >>=
      Runtime.return_term

    | TT.Syntax.Lambda (x, None, _) ->
      Runtime.(error ~loc (UnannotatedLambda x))

    | TT.Syntax.Lambda (x, Some u, c) ->
      check_ty u >>= fun ju ->
      Runtime.add_free ~loc:(u.Location.loc) x ju (fun jy ->
      let vy = Jdg.atom_term ~loc:(u.Location.loc) jy in
      Predefined.add_abstracting vy
      (infer c >>= as_term ~loc:(c.Location.loc) >>= fun je ->
      jdg_form ~loc (Jdg.Lambda (jy, je)) >>=
      Runtime.return_term))

    | TT.Syntax.Prod (x,u,c) ->
      check_ty u >>= fun ju ->
      Runtime.add_free ~loc:u.Location.loc x ju (fun jy ->
      let vy = Jdg.atom_term ~loc:(u.Location.loc) jy in
      Predefined.add_abstracting vy
      (check_ty c >>= fun jt ->
      jdg_form ~loc (Jdg.Prod (jy, jt)) >>=
      Runtime.return_term))

    | TT.Syntax.Eq (c1, c2) ->
       infer c1 >>= as_term ~loc:c1.Location.loc >>= fun j1 ->
       let t1 = Jdg.typeof j1 in
       check c2 t1 >>= fun j2 ->
       jdg_form ~loc (Jdg.Eq (j1,j2)) >>=
       Runtime.return_term

    | TT.Syntax.Refl c ->
       infer c >>= as_term ~loc:c.Location.loc >>= fun j ->
       jdg_form ~loc (Jdg.Refl j) >>=
       Runtime.return_term

    | TT.Syntax.CongrProd (c1, c2, c3) ->
      infer c1 >>= as_atom ~loc:c1.Location.loc >>= fun x ->
      infer c2 >>= as_term ~loc:c2.Location.loc >>= fun ja ->
      infer c3 >>= as_term ~loc:c3.Location.loc >>= fun jb ->
      let eqa = Jdg.reflect_ty_eq ~loc:c2.Location.loc ja
      and eqb = Jdg.reflect_ty_eq ~loc:c3.Location.loc jb in
      let eq = Jdg.congr_prod_ty ~loc eqa x x eqb in
      let e = Jdg.refl_of_eq_ty ~loc eq in
      Runtime.return_term e

    | TT.Syntax.CongrApply (c1, c2, c3, c4, c5) ->
      infer c1 >>= as_atom ~loc:c1.Location.loc >>= fun x ->
      infer c2 >>= as_term ~loc:c2.Location.loc >>= fun jh ->
      infer c3 >>= as_term ~loc:c3.Location.loc >>= fun jarg ->
      infer c4 >>= as_term ~loc:c4.Location.loc >>= fun ja ->
      infer c5 >>= as_term ~loc:c5.Location.loc >>= fun jb ->
      let eqh = Jdg.reflect ~loc:c2.Location.loc jh
      and eqarg = Jdg.reflect ~loc:c3.Location.loc jarg
      and eqa = Jdg.reflect_ty_eq ~loc:c4.Location.loc ja
      and eqb = Jdg.reflect_ty_eq ~loc:c5.Location.loc jb in
      let eq = Jdg.congr_apply ~loc eqa x x eqb eqh eqarg in
      let e = Jdg.refl_of_eq ~loc eq in
      Runtime.return_term e

    | TT.Syntax.CongrLambda (c1, c2, c3, c4) ->
      infer c1 >>= as_atom ~loc:c1.Location.loc >>= fun x ->
      infer c2 >>= as_term ~loc:c2.Location.loc >>= fun ja ->
      infer c3 >>= as_term ~loc:c3.Location.loc >>= fun jb ->
      infer c4 >>= as_term ~loc:c4.Location.loc >>= fun jbody ->
      let eqbody = Jdg.reflect ~loc:c4.Location.loc jbody
      and eqa = Jdg.reflect_ty_eq ~loc:c2.Location.loc ja
      and eqb = Jdg.reflect_ty_eq ~loc:c3.Location.loc jb in
      let eq = Jdg.congr_lambda ~loc eqa x x eqb eqbody in
      let e = Jdg.refl_of_eq ~loc eq in
      Runtime.return_term e

    | TT.Syntax.CongrEq (c1, c2, c3) ->
      infer c1 >>= as_term ~loc:c1.Location.loc >>= fun jt ->
      infer c2 >>= as_term ~loc:c2.Location.loc >>= fun jlhs ->
      infer c3 >>= as_term ~loc:c3.Location.loc >>= fun jrhs ->
      let eqt = Jdg.reflect_ty_eq ~loc:c1.Location.loc jt
      and eqlhs = Jdg.reflect ~loc:c2.Location.loc jlhs
      and eqrhs = Jdg.reflect  ~loc:c3.Location.loc jrhs in
      let eq = Jdg.congr_eq_ty ~loc eqt eqlhs eqrhs in
      let e = Jdg.refl_of_eq_ty ~loc eq in
      Runtime.return_term e

    | TT.Syntax.CongrRefl (c1, c2) ->
      infer c1 >>= as_term ~loc:c1.Location.loc >>= fun jt ->
      infer c2 >>= as_term ~loc:c2.Location.loc >>= fun je ->
      let eqt = Jdg.reflect_ty_eq ~loc:c1.Location.loc jt
      and eqe = Jdg.reflect ~loc:c2.Location.loc je in
      let eq = Jdg.congr_refl ~loc eqt eqe in
      let e = Jdg.refl_of_eq ~loc eq in
      Runtime.return_term e

    | TT.Syntax.BetaStep (c1, c2, c3, c4, c5) ->
      infer c1 >>= as_atom ~loc:c1.Location.loc >>= fun x ->
      infer c2 >>= as_term ~loc:c2.Location.loc >>= fun ja ->
      infer c3 >>= as_term ~loc:c3.Location.loc >>= fun jb ->
      infer c4 >>= as_term ~loc:c4.Location.loc >>= fun jbody ->
      infer c5 >>= as_term ~loc:c5.Location.loc >>= fun jarg ->
      let eqa = Jdg.reflect_ty_eq ~loc:c2.Location.loc ja
      and eqb = Jdg.reflect_ty_eq ~loc:c3.Location.loc jb in
      let eq = Jdg.beta ~loc eqa x x eqb jbody jarg in
      let e = Jdg.refl_of_eq ~loc eq in
      Runtime.return_term e


(* XXX: Copy and paste from eval.ml *)
let check_default_v ~loc v t_check =
  as_term ~loc v >>= fun je ->
  Equal.coerce ~loc je t_check >>=
    begin function
      | Some je -> Runtime.return je
      | None -> Jdg.errorTypeMismatchCheckingMode ~loc je t_check
  end

let check_default ~loc (check, check_ty, infer) ttc t_check =
  inferTT ~loc (check, check_ty, infer) ttc >>= fun v ->
  check_default_v ~loc v t_check

(* check_lambda: loc:Location.t -> Jdg.ty -> ... -> Name.ident
                   -> 'annot Syntax.comp option -> 'annot Syntax.comp
                   -> Jdg.term Runtime.comp *)
let check_lambda ~loc (check, check_ty, _) t_check x u c =
  Equal.as_prod ~loc t_check >>= function
    | None -> Jdg.errorProductExpected ~loc t_check
    | Some (eq, a, b) ->
      begin match u with
        | Some u ->
          check_ty u >>= fun ju ->
          Equal.equal_ty ~loc:(u.Location.loc) ju (Jdg.atom_ty a) >>= begin function
            | Some equ -> Runtime.return (ju, equ)
            | None -> Jdg.errorAnnotationMismatch ~loc:(u.Location.loc) ju (Jdg.atom_ty a)
            end
        | None ->
          let ju = Jdg.atom_ty a in
          let equ = Jdg.reflexivity_ty ju in
          Runtime.return (ju, equ)
      end >>= fun (ju, equ) -> (* equ : ju == typeof a *)
      Runtime.add_free ~loc x ju (fun jy ->
      Predefined.add_abstracting (Jdg.atom_term ~loc jy)
      (let b = Jdg.substitute_ty ~loc b a (Jdg.convert ~loc (Jdg.atom_term ~loc jy) equ) in
      check c b >>= fun e ->
      jdg_form ~loc (Jdg.Lambda (jy, e)) >>= fun lam ->
      let eq_prod = Jdg.congr_prod_ty ~loc equ jy a (Jdg.reflexivity_ty b) in
      let lam = Jdg.convert ~loc lam eq_prod in
      let lam = Jdg.convert ~loc lam (Jdg.symmetry_ty eq) in
      Runtime.return lam))



let checkTT ~loc (check, check_ty, infer) ttc t_check =
  match ttc with
      TT.Syntax.Type
    | TT.Syntax.Constant _
    | TT.Syntax.Prod _
    | TT.Syntax.Eq _
    | TT.Syntax.CongrProd _
    | TT.Syntax.CongrApply _
    | TT.Syntax.CongrLambda _
    | TT.Syntax.CongrEq _
    | TT.Syntax.CongrRefl _
    | TT.Syntax.BetaStep _ ->
        check_default ~loc (check, check_ty, infer) ttc t_check

    | TT.Syntax.Lambda (x,u,c) ->
      check_lambda ~loc (check, check_ty, infer) t_check x u c

    | TT.Syntax.Refl c ->
      Equal.as_eq ~loc t_check >>= begin function
        | None -> Jdg.errorEqualityTypeExpected ~loc t_check
        | Some (eq, e1, e2) ->
          let t = Jdg.typeof e1 in
          check c t >>= fun e ->
          Equal.equal ~loc e e1 >>= begin function
            | None -> Jdg.errorEqualityFail ~loc e e1
            | Some eq1 ->
              Equal.equal ~loc e e2 >>= begin function
                | None -> Jdg.errorEqualityFail ~loc e e2
                | Some eq2 ->
                  let j = Jdg.mk_refl ~loc eq1 eq2 in
                  let j = Jdg.convert ~loc j (Jdg.symmetry_ty eq) in
                  Runtime.return j
                end
            end
        end


