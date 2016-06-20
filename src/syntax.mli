(** Desugared input syntax *)

(** Bound variables are de Bruijn indices *)
type bound = int

(** AML type declarations are referred to by de Bruijn levels *)
type level = int

type 'a located = 'a Location.located

type ml_ty = ml_ty' located
and ml_ty' =
  | ML_Arrow of ml_ty * ml_ty
  | ML_Prod of ml_ty list
  | ML_TyApply of Name.ident * level * ml_ty list
  | ML_Handler of ml_ty * ml_ty
  | ML_Judgment
  | ML_String
  | ML_Bound of bound
  | ML_Anonymous

type ml_schema = ml_schema' located
and ml_schema' = ML_Forall of Name.ty list * ml_ty


type pattern = pattern' located
and pattern' =
  | Patt_Anonymous
  | Patt_As of pattern * bound
  | Patt_Bound of bound
  | Patt_Jdg of TT.Syntax.jdg_pattern
  | Patt_Constructor of Name.ident * pattern list
  | Patt_Tuple of pattern list

(** Desugared 'annot computations *)
type 'annot comp = 'annot comp' located
and 'annot comp' =
  | Bound of bound
  | Function of Name.ident * 'annot comp
  | Apply of 'annot comp * 'annot comp
  | Handler of 'annot handler
  | Yield of 'annot comp
  | Constructor of Name.ident * 'annot comp list
  | Tuple of 'annot comp list
  | Operation of Name.ident * 'annot comp list
  | With of 'annot comp * 'annot comp
  | Let of 'annot let_clause list * 'annot comp
  | LetRec of 'annot letrec_clause list * 'annot comp
  | Now of bound * 'annot comp * 'annot comp
  | Lookup of 'annot comp
  | Update of 'annot comp * 'annot comp
  | Ref of 'annot comp
  | Sequence of 'annot comp * 'annot comp
  | String of string
  | External of string
  | Match of 'annot comp * 'annot match_case list

  | TTc of ('annot comp) TT.Syntax.comp

and 'annot let_clause = Name.ident * 'annot * 'annot comp

and 'annot letrec_clause = Name.ident * Name.ident * 'annot * 'annot comp

and 'annot handler = {
  handler_val: 'annot match_case list;
  handler_ops: 'annot match_op_case list Name.IdentMap.t;
  handler_finally : 'annot match_case list;
}

and 'annot match_case = Name.ident list * pattern * 'annot comp

(** Match multiple patterns at once, with shared pattern variables *)
and 'annot match_op_case = Name.ident list * pattern list * pattern option * 'annot comp

type 'annot top_op_case = Name.ident list * Name.ident option * 'annot comp

type constructor_decl = Name.constructor * ml_ty list

type ml_tydef =
  | ML_Sum of constructor_decl list
  | ML_Alias of ml_ty

(** Desugared toplevel commands *)
type 'annot toplevel = 'annot toplevel' located
and 'annot toplevel' =
  | DefMLType of (Name.ty * (Name.ty list * ml_tydef)) list
  | DefMLTypeRec of (Name.ty * (Name.ty list * ml_tydef)) list
  | DeclOperation of Name.operation * (ml_ty list * ml_ty)
  | DeclConstants of Name.constant list * 'annot comp
  | TopHandle of (Name.operation * 'annot top_op_case) list
  | TopLet of 'annot let_clause list
  | TopLetRec of 'annot letrec_clause list
  | TopDynamic of Name.ident * 'annot * 'annot comp
  | TopNow of bound * 'annot comp
  | TopDo of 'annot comp
  | TopFail of 'annot comp
  | Verbosity of int
  | Included of (string * 'annot toplevel list) list

