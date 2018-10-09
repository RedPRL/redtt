open RedBasis
open RedTT_Core

type 'a info =
  {con : 'a;
   span : Log.location}

type mlname = [`Gen of Name.t | `User of string]

type primdata =
  | PrimString of string
  | PrimFloat of float
  | PrimRef of Name.t
  | PrimTuple of primdata list

type mlval =
  | MlDataDesc of Desc.desc
  | MlTerm of Tm.tm
  | MlSys of (Tm.tm, Tm.tm) Tm.system
  | MlThunk of mlcmd
  | MlVar of mlname
  | MlRef of Name.t
  | MlTuple of mlval list
  | MlString of string
  | MlFloat of float

and mlcmd =
  | MlRet of mlval
  | MlLam of mlname * mlcmd
  | MlApp of mlcmd * mlval
  | MlElab of escheme * eterm
  | MlCheck of {ty : mlval; tm : mlval}
  | MlDeclData of {name : string; desc : edesc}
  | MlDefine of {name : mlval; opacity : [`Opaque | `Transparent]; ty : mlval; tm : mlval}
  | MlSplit of mlval * mlname list * mlcmd
  | MlUnify
  | MlBind of mlcmd * mlname * mlcmd
  | MlUnleash of mlval
  | MlNormalize of mlval
  | MlImport of string
  | MlPrint of mlval info
  | MlForeign of (primdata -> mlcmd) * mlval

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
  | RunML of mlcmd

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

let ml_get_time =
  let f _ = MlRet (MlFloat (Unix.gettimeofday ())) in
  MlForeign (f, MlTuple [])

let ml_print_bench name now0 now1 =
  let f = function
    | PrimTuple [PrimRef name; PrimFloat now0; PrimFloat now1] ->
      Format.printf "Defined %a (%fs).@." Name.pp name (now1 -. now0);
      MlRet (MlTuple [])
    | _ ->
      failwith "ml_print_bench"
  in
  MlForeign (f, MlTuple [name; now0; now1])


let define ~name ~opacity ~scheme ~tm =
  mlbind ml_get_time @@ fun now0 ->
  mlbind (MlElab (scheme, tm)) @@ fun x ->
  mlsplit x @@ fun ty tm ->
  mlbind (MlDefine {name; ty; tm; opacity}) @@ fun _ ->
  mlbind MlUnify @@ fun _ ->
  mlbind ml_get_time @@ fun now1 ->
  mlbind (ml_print_bench name now0 now1) @@ fun _ ->
  MlRet x


module Env = PersistentTable.M
module Sem =
struct
  type t =
    | DataDesc of Desc.desc
    | Term of Tm.tm
    | Sys of (Tm.tm, Tm.tm) Tm.system
    | Ref of Name.t
    | Thunk of mlenv * mlcmd
    | Tuple of t list
    | Clo of mlenv * mlname * mlcmd
    | String of string
    | Float of float

  and mlenv = (mlname, t) Env.t

  let rec pp fmt =
    function
    | DataDesc desc ->
      Desc.pp_desc Pp.Env.emp fmt desc
    | Term tm ->
      Tm.pp0 fmt tm
    | Sys sys ->
      Format.fprintf fmt "@[<hv1>[%a]@]" (Tm.pp_sys Pp.Env.emp) sys
    | Ref a ->
      Name.pp fmt a
    | Clo _ ->
      Format.fprintf fmt "<clo>"
    | Thunk _ ->
      Format.fprintf fmt "<thunk>"
    | Tuple vs ->
      let comma fmt () = Format.fprintf fmt ",@ " in
      let pp_cells = Format.pp_print_list ~pp_sep:comma pp in
      Format.fprintf fmt "@[<hv1><%a>@]" pp_cells vs
    | String str ->
      Format.fprintf fmt "'%a'" Uuseg_string.pp_utf_8 str
    | Float x ->
      Format.fprintf fmt "%f" x

  let unleash_term =
    function
    | Term tm -> tm
    | _ -> failwith "unleash_term"

  let unleash_ref =
    function
    | Ref x -> x
    | _ -> failwith "unleash_ref"
end
