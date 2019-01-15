open RedBasis
open RedTT_Core
open Bwd

type 'a info =
  {con : 'a;
   span : Log.location}

module T = PersistentTable.M
type mlconf =
  | TopModule of {indent : string}
  | InMem of {stem : FileRes.filepath; indent : string}
  | InFile of {stem : FileRes.filepath; redsum : Digest.t; indent : string}
exception WrongMode (** executing a top command in a file scope or vice versa. *)

type mlname = [`Gen of Name.t | `User of string]


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
  | MlConf of mlconf

and mlcmd =
  | MlTopLoadFile of FileRes.filepath
  | MlTopLoadStdin of {red : FileRes.filepath}

  | MlRet of mlval
  | MlLam of mlname * mlcmd
  | MlApp of mlcmd * mlval
  | MlElab of eterm
  | MlElabWithScheme of escheme * eterm
  | MlCheck of {ty : mlval; tm : mlval}
  | MlDeclData of {visibility : ResEnv.visibility; name : mlval; desc : edesc}
  | MlDefine of {visibility : ResEnv.visibility; name : mlval; opacity : [`Opaque | `Transparent]; ty : mlval; tm : mlval}
  | MlSplit of mlval * mlname list * mlcmd
  | MlUnify
  | MlBind of mlcmd * mlname * mlcmd
  | MlUnleash of mlval
  | MlNormalize of mlval
  | MlImport of ResEnv.visibility * FileRes.selector
  | MlPrint of mlval info
  | MlDebug of [`All | `Constraints | `Unsolved]
  | MlForeign of (semval -> mlcmd) * mlval
  | MlGetConf

and semcmd =
  | SemRet of semval
  | SemClo of mlenv * mlname * mlcmd
  | SemElabClo of mlenv * eterm

and semval =
  | SemDataDesc of Desc.desc
  | SemTerm of Tm.tm
  | SemSys of (Tm.tm, Tm.tm) Tm.system
  | SemRef of Name.t
  | SemThunk of mlenv * mlcmd
  | SemTuple of semval list
  | SemString of string
  | SemFloat of float
  | SemConf of mlconf

and mlenv =
  {values : (mlname, semval) T.t;
   imported_modules : FileRes.selector bwd;
   mlconf : mlconf}

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

  | V of {x : string; ty0 : eterm; ty1 : eterm; equiv : eterm}

  | Box of {cap : eterm; sys : eterm list}

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
  | VProj
  | Cap
  | Open

module Env :
sig
  type t = mlenv
  val init : mlconf : mlconf -> t
  val mlconf : t -> mlconf
  val indent : mlconf -> string
  val stem : mlconf -> FileRes.filepath
  val set : mlname -> semval -> t -> t
  val find : mlname -> t -> semval option
  val record_import : FileRes.selector -> t -> t
  val imports : t -> FileRes.selector list
end =
struct
  type t = mlenv

  let init ~mlconf = {values = T.init ~size:100; imported_modules = Emp; mlconf}

  let mlconf {mlconf; _} = mlconf

  let indent =
    function
    | TopModule {indent} -> indent
    | InFile {indent; _} -> indent
    | InMem {indent; _} -> indent
  let stem =
    function
    | TopModule _ -> invalid_arg "Env.stem"
    | InFile {stem; _} -> stem
    | InMem {stem; _} -> stem

  let set k v e = {e with values = T.set k v e.values}
  let find k e = T.find k e.values

  let record_import sel env = {env with imported_modules = Snoc (env.imported_modules, sel)}
  let imports env = Bwd.to_list env.imported_modules
end

(* Please fill this in. I'm just using it for debugging. *)
let rec pp fmt =
  function
  | Hole _ ->
    Format.fprintf fmt "<hole>"
  | Hope ->
    Format.fprintf fmt "<hope>"
  | Guess _ ->
    Format.fprintf fmt "<guess>"

  | Var {name; _} ->
    Format.fprintf fmt "%s" name
  | Num _ ->
    Format.fprintf fmt "<num>"

  | Pi _ ->
    Format.fprintf fmt "<pi>"
  | Sg _ ->
    Format.fprintf fmt "<sg>"
  | Ext _ ->
    Format.fprintf fmt "<ext>"

  | Lam _ ->
    Format.fprintf fmt "<lam>"
  | Tuple _ ->
    Format.fprintf fmt "<tuple>"

  | Coe _ ->
    Format.fprintf fmt "<coe>"
  | HCom _ ->
    Format.fprintf fmt "<hcom>"
  | Com _ ->
    Format.fprintf fmt "<com>"

  | Type _ ->
    Format.fprintf fmt "<type>"

  | Box {cap; sys} ->
    Format.fprintf fmt "@[box@ %a@ [%a]@]" pp cap.con (ListUtil.pp "|" pp_eterm) sys

  | V _ ->
    Format.fprintf fmt "<V>"

  | Elim _ ->
    Format.fprintf fmt "<elim>"
  | ElimFun _ ->
    Format.fprintf fmt "<elim-fun>"

  | Let _ ->
    Format.fprintf fmt "<let>"
  | Cut (hd, stk) ->
    Format.fprintf fmt "@[<hov1>(cut@ %a@ %a)@]" pp_eterm hd (ListUtil.pp " " pp_frame) stk

  | Refl ->
    Format.fprintf fmt "refl"
  | Quo _ ->
    Format.fprintf fmt "<quo>"
  | RunML _ ->
    Format.fprintf fmt "<run-ml>"

and pp_eterm fmt {con; _} = pp fmt con

and pp_frame fmt =
  function
  | App e -> pp_eterm fmt e
  | Fst -> Format.fprintf fmt "fst"
  | Snd -> Format.fprintf fmt "snd"
  | VProj -> Format.fprintf fmt "vproj"
  | Cap -> Format.fprintf fmt "cap"
  | Open -> Format.fprintf fmt "open"

let pp_edecl fmt =
  function
  | MlImport (vis, sel) ->
    Format.fprintf fmt "%a import %a" ResEnv.pp_visibility vis FileRes.pp_selector sel
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

let ml_print_bench conf name now0 now1 =
  let f = function
    | SemTuple [SemConf mlconf; SemRef name; SemFloat now0; SemFloat now1] ->
      Format.printf "@[%sDefined %a (%fs).@]@." (Env.indent mlconf) Name.pp name (now1 -. now0);
      MlRet (MlTuple [])
    | _ ->
      failwith "ml_print_bench"
  in
  MlForeign (f, MlTuple [conf; name; now0; now1])


let define ~visibility ~name ~opacity ~scheme ~tm =
  mlbind ml_get_time @@ fun now0 ->
  mlbind (MlElabWithScheme (scheme, tm)) @@ fun x ->
  mlsplit x @@ fun ty tm ->
  mlbind (MlDefine {name; ty; tm; visibility; opacity}) @@ fun _ ->
  mlbind MlUnify @@ fun _ ->
  mlbind ml_get_time @@ fun now1 ->
  mlbind MlGetConf @@ fun conf ->
  mlbind (ml_print_bench conf name now0 now1) @@ fun _ ->
  MlRet x



let rec pp_semcmd fmt =
  function
  | SemRet v ->
    pp_semval fmt v
  | SemClo _ ->
    Format.fprintf fmt "<clo>"
  | SemElabClo _ ->
    Format.fprintf fmt "<elab-clo>"

and pp_semval fmt =
  function
  | SemDataDesc desc ->
    Desc.pp_desc Pp.Env.emp fmt desc
  | SemTerm tm ->
    Tm.pp0 fmt tm
  | SemSys sys ->
    Format.fprintf fmt "@[<hv1>[%a]@]" (Tm.pp_sys Pp.Env.emp) sys
  | SemRef a ->
    Name.pp fmt a
  | SemThunk _ ->
    Format.fprintf fmt "<thunk>"
  | SemTuple vs ->
    let comma fmt () = Format.fprintf fmt ",@ " in
    let pp_cells = Format.pp_print_list ~pp_sep:comma pp_semval in
    Format.fprintf fmt "@[<hv1><%a>@]" pp_cells vs
  | SemString str ->
    Format.fprintf fmt "\"%a\"" Uuseg_string.pp_utf_8 str
  | SemFloat x ->
    Format.fprintf fmt "%f" x
  | SemConf x ->
    Format.fprintf fmt "<mlconf>"

let unleash_term =
  function
  | SemTerm tm -> tm
  | _ -> failwith "unleash_term"

let unleash_ref =
  function
  | SemRef x -> x
  | _ -> failwith "unleash_ref"
