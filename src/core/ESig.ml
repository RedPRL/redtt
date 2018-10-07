open RedBasis

type 'a info =
  {con : 'a;
   span : Log.location}

type mlname = [`Gen of Name.t | `User of string]

type mlval =
  | MlDataDesc of Desc.desc
  | MlTerm of Tm.tm
  | MlSys of (Tm.tm, Tm.tm) Tm.system
  | MlThunk of mlcmd
  | MlVar of mlname
  | MlRef of Name.t
  | MlTuple of mlval list

and mlcmd =
  | MlRet of mlval
  | MlLam of mlname * mlcmd
  | MlApp of mlcmd * mlval
  | MlElab of escheme * eterm
  | MlDefine of {name : mlval; opacity : [`Opaque | `Transparent]; ty : mlval; tm : mlval}
  | MlSplit of mlval * mlname list * mlcmd
  | MlUnify
  | MlBind of mlcmd * mlname * mlcmd
  | MlUnleash of mlval
  | MlNormalize of eterm
  | MlImport of string

and edesc =
    EDesc of
      {kind : Kind.t;
       lvl : Lvl.t;
       params : ecell list;
       constrs : (string * econstr) list}

and econstr =
    EConstr of
      {specs : ecell list;
       boundary : esys}

and escheme =
  etele * eterm

and ecell =
  [ `Ty of string * eterm
  | `Tick of string
  | `I of string
  ]

and etele = ecell list

and econ =
  | Guess of eterm
  | Hole of string option * eterm option
  | Hope
  | Lam of einvpat list * eterm
  | Tuple of eterm list
  | Type of Kind.t * Lvl.t
  | Quo of (ResEnv.t -> Tm.tm)
  | Let of {pat : einvpat; sch : escheme; tm : eterm; body : eterm}

  | Elim of {mot : eterm option; scrut : eterm; clauses : eclause list}
  | ElimFun of {clauses : eclause list}

  | Pi of etele * eterm
  | Sg of etele * eterm
  | Ext of string list * eterm * esys

  | Coe of {r : eterm; r' : eterm; fam : eterm; tm : eterm}
  | HCom of {r : eterm; r' : eterm; cap : eterm; sys : esys}
  | Com of {r : eterm; r' : eterm; fam : eterm; cap : eterm; sys : esys}

  | Shut of eterm

  | DFixLine of {r : eterm; name : string; ty : eterm; bdy : eterm}
  | FixLine of {r : eterm; name : string; ty : eterm; bdy : eterm}

  | Cut of eterm * frame list

  | Refl

  | Var of {name : string; ushift : int}
  | Num of int

  (* To run a metalanguage tactic *)
  | RunML of mlval

and eterm = econ info

and eclause =
  [ `Con of string * einvpat epatbind list * eterm
  | `All of eterm
  ]

and 'a epatbind =
  [ `Bind of 'a
  | `BindIH of 'a * 'a
  ]

and einvpat =
  [ `Var of [`User of string | `Gen of Name.t]
  | `SplitAs of einvpat * einvpat
  | `Split
  | `Bite of einvpat
  | `Wildcard
  ]

and esys = eface list

and eface = (eterm * eterm) list * eterm

and frame =
  | App of eterm
  | Fst
  | Snd
  | Open


(* Please fill this in. I'm just using it for debugging. *)
let pp fmt =
  function
  | Hole _ ->
    Format.fprintf fmt "<hole>"
  | Hope ->
    Format.fprintf fmt "<hope>"
  | Lam _ ->
    Format.fprintf fmt "<lam>"
  | Var {name; _} ->
    Format.fprintf fmt "%s" name
  | _ ->
    Format.fprintf fmt "<eterm>"

let pp_edecl fmt =
  function
  | MlImport str ->
    Format.fprintf fmt "import %s" str
  | _ ->
    Format.fprintf fmt "<other>"

let pp_esig =
  Pp.pp_list pp_edecl



let mlbind cmd f =
  let x = `Gen (Name.fresh ()) in
  MlBind (cmd, x, f (MlVar x))

let mlsplit v f =
  let x = `Gen (Name.fresh ()) in
  let y = `Gen (Name.fresh ()) in
  MlSplit (v, [x; y], f (MlVar x) (MlVar y))

let define ~name ~opacity ~scheme ~tm =
  mlbind (MlElab (scheme, tm)) @@ fun x ->
  mlsplit x @@ fun ty tm ->
  mlbind (MlDefine {name; ty; tm; opacity}) @@ fun _ ->
  MlUnify


module MlEnv = PersistentTable.M
module MlSem =
struct
  type t =
    | DataDesc of Desc.desc
    | Term of Tm.tm
    | Sys of (Tm.tm, Tm.tm) Tm.system
    | Ref of Name.t
    | Thunk of mlenv * mlcmd
    | Tuple of t list
    | Clo of mlenv * mlname * mlcmd

  and mlenv = (mlname, t) MlEnv.t

  let unleash_term =
    function
    | Term tm -> tm
    | _ -> failwith "unleash_term"

  let unleash_ref =
    function
    | Ref x -> x
    | _ -> failwith "unleash_ref"
end
