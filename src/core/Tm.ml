open RedBasis
open Bwd
open BwdNotation

include TmData

(* Info we will store inside the term nodes to enable optimizations *)
module Info :
sig
  type t
  val init : t
  val with_ix : int -> t
  val mergen : t list -> t
  val bind : int -> t -> t

  val is_locally_closed : t -> bool
end =
struct

  module Ix =
  struct
    type t =
      | Closed
      | MaxIx of int

    let bind n =
      function
      | Closed ->
        Closed
      | MaxIx ix ->
        let ix' = ix - n in
        if ix' < 0 then Closed else MaxIx ix'

    let merge i0 i1 =
      match i0, i1 with
      | Closed, MaxIx ix -> i1
      | MaxIx ix, Closed -> i0
      | Closed, Closed -> Closed
      | MaxIx ix0, MaxIx ix1 ->
        MaxIx (max ix0 ix1)
  end

  type t = {ix_info : Ix.t}

  let is_locally_closed info =
    match info.ix_info with
    | Ix.Closed -> true
    | _ -> false

  let init =
    {ix_info = Ix.Closed}

  let with_ix ix =
    {ix_info = Ix.MaxIx ix}

  let bind n info =
    {ix_info = Ix.bind n info.ix_info}

  let merge i0 i1 =
    {ix_info = Ix.merge i0.ix_info i1.ix_info}

  let mergen =
    List.fold_left merge init
end

type tm = Tm of {con : tm tmf; info : Info.t}

type btm = tm Desc.Boundary.term
type bface = (tm, btm) Desc.Boundary.face
type bsys = (tm, btm) Desc.Boundary.sys
type data_desc = (tm, btm) Desc.desc

type 'a subst =
  | Shift of int
  | Dot of 'a * 'a subst
  | Cmp of 'a subst * 'a subst

let shift i = Shift i
let dot a sb = Dot (a, sb)


type error =
  | InvalidDeBruijnIndex of int
  | UnbindLengthMismatch of tm cmd list * tm nbnd
  | UnbindExtLengthMismatch of tm cmd list * (tm * (tm, tm) system) nbnd

exception E of error

let ix ?twin:(tw = `Only) i =
  Ix (i, tw), Emp

let var ?twin:(tw = `Only) a =
  Var {name = a; twin = tw; ushift = 0}, Emp

let rec con_info =
  function
  | FHCom {r; r'; cap; sys} ->
    Info.mergen [tm_info r; tm_info r'; tm_info cap; sys_info (bnd_info tm_info) sys]
  | Univ _ | Dim0 | Dim1 | Data _ ->
    Info.init
  | Pi (dom, cod) | Sg (dom, cod) ->
    Info.mergen [tm_info dom; bnd_info tm_info cod]
  | Ext bnd ->
    nbnd_info ext_info bnd
  | Restrict face | RestrictThunk face ->
    face_info tm_info face
  | V {r; ty0; ty1; equiv} ->
    Info.mergen [tm_info r; tm_info ty0; tm_info ty1; tm_info equiv]
  | VIn {r; tm0; tm1} ->
    Info.mergen [tm_info r; tm_info tm0; tm_info tm1]
  | Lam bnd | Later bnd | Next bnd ->
    bnd_info tm_info bnd
  | ExtLam nbnd ->
    nbnd_info tm_info nbnd
  | Cons (t0, t1) ->
    Info.mergen [tm_info t0; tm_info t1]
  | Box {r; r'; cap; sys} ->
    Info.mergen [tm_info r; tm_info r'; tm_info cap; sys_info tm_info sys]
  | LblTy {args; ty; _} ->
    Info.mergen @@ tm_info ty :: List.map (pair_info tm_info tm_info) args
  | LblRet t ->
    tm_info t
  | Up cmd ->
    cmd_info cmd
  | Let (cmd, bnd) ->
    Info.mergen [cmd_info cmd; bnd_info tm_info bnd]
  | Intro (_, _, ts) ->
    Info.mergen @@ List.map tm_info ts

and cmd_info cmd =
  pair_info head_info (bwd_info frame_info) cmd

and head_info =
  function
  | Meta _ | Var _ ->
    Info.init
  | Ix (i, _) ->
    Info.with_ix i
  | Down {ty; tm} ->
    Info.mergen [tm_info ty; tm_info tm]
  | DownX tm ->
    tm_info tm
  | DFix {r; ty; bdy} ->
    Info.mergen [tm_info r; tm_info ty; bnd_info tm_info bdy]
  | Coe {r; r'; ty; tm} ->
    Info.mergen [tm_info r; tm_info r'; bnd_info tm_info ty; tm_info tm]
  | HCom {r; r'; ty; cap; sys} | GHCom {r; r'; ty; cap; sys} ->
    Info.mergen [tm_info r; tm_info r'; tm_info cap; tm_info ty; sys_info (bnd_info tm_info) sys]
  | Com {r; r'; ty; cap; sys} | GCom {r; r'; ty; cap; sys} ->
    Info.mergen [tm_info r; tm_info r'; tm_info cap; bnd_info tm_info ty; sys_info (bnd_info tm_info) sys]


and frame_info =
  function
  | Car | Cdr | LblCall | RestrictForce ->
    Info.init
  | FunApp t ->
    tm_info t
  | ExtApp ts ->
    Info.mergen @@ List.map tm_info ts
  | Cap {r; r'; ty; sys} ->
    Info.mergen [tm_info r; tm_info r'; tm_info ty; sys_info (bnd_info tm_info) sys]
  | VProj {r; func} ->
    Info.mergen [tm_info r; tm_info func]
  | Prev t ->
    tm_info t
  | Elim {dlbl; mot; clauses} ->
    let clause_info (_, nbnd) = nbnd_info tm_info nbnd in
    Info.mergen @@ bnd_info tm_info mot :: List.map clause_info clauses

and bwd_info : type x. (x -> Info.t) -> x bwd -> Info.t =
  fun f xs ->
    Info.mergen @@ Bwd.to_list @@ Bwd.map f xs

and pair_info : type x y. (x -> Info.t) -> (y -> Info.t) -> x * y -> Info.t =
  fun f g (a, b) ->
    Info.mergen [f a; g b]

and bnd_info f (B (_, t)) =
  Info.bind 1 @@ f t

and nbnd_info : type x. (x -> Info.t) -> x nbnd -> Info.t =
  fun f (NB (nms, t)) ->
    Info.bind (Bwd.length nms) @@ f t

and ext_info (ty, sys) =
  Info.mergen [tm_info ty; sys_info tm_info sys]

and sys_info : type x. (x -> Info.t) -> (tm, x) system -> Info.t =
  fun f sys ->
    Info.mergen @@ List.map (face_info f) sys

and face_info : type x. (x -> Info.t) -> (tm, x) face -> Info.t =
  fun f (r, r', o) ->
    match o with
    | None ->
      Info.mergen [tm_info r; tm_info r']
    | Some x ->
      Info.mergen [tm_info r; tm_info r'; f x]


and tm_info (Tm node) =
  node.info


let make con =
  let exception Make of tm tmf in
  let compress =
    function
    | Up (Down {tm = Tm {con = Up (hd, sp'); _}; _}, sp) ->
      raise @@ Make (Up (hd, sp' <.> sp))
    | Up (Down {tm; _}, Emp) ->
      tm
    | con ->
      raise @@ Make con
  in
  match compress con with
  | tm -> tm
  | exception (Make con) ->
    Tm {con; info = con_info con}


(* "algebras" for generic traversals of terms; the interface is imperative, because
   the monadic / functional version had prohibitively bad performance.
   Consider refactoring these into OCaml's object system (who know one could ever
   find a use for that!). *)
module type Alg =
sig
  val with_bindings : int -> (unit -> 'a) -> 'a
  val under_meta : (unit -> 'a) -> 'a
  val should_traverse : Info.t -> bool

  val bvar : ih:(tm cmd -> tm cmd) -> ix:int -> twin:twin -> tm cmd
  val fvar : name:Name.t -> twin:twin -> ushift:int -> tm cmd
  val meta : name:Name.t -> ushift:int -> tm cmd
end


module Traverse (A : Alg) : sig
  val traverse_tm : tm -> tm
  val traverse_head : tm head -> tm cmd
  val traverse_spine : tm spine -> tm spine
  val traverse_cmd : tm cmd -> tm cmd
end =
struct
  let rec traverse_tm (Tm info) =
    if A.should_traverse info.info then
      let con' = traverse_con info.con in
      make @@ con'
    else
      Tm info

  and traverse_con =
    function
    | (Univ _ | Dim0 | Dim1 as con) ->
      con

    | FHCom info ->
      let r = traverse_tm info.r in
      let r' = traverse_tm info.r' in
      let cap = traverse_tm info.cap in
      let sys = traverse_list traverse_bface info.sys in
      FHCom {r; r'; cap; sys}

    | Pi (dom, cod) ->
      let dom' = traverse_tm dom in
      let cod' = traverse_bnd traverse_tm cod in
      Pi (dom', cod')

    | Sg (dom, cod) ->
      let dom' = traverse_tm dom in
      let cod' = traverse_bnd traverse_tm cod in
      Sg (dom', cod')

    | Ext ebnd ->
      let ebnd' =
        traverse_nbnd
          (traverse_pair traverse_tm (traverse_list traverse_face))
          ebnd
      in
      Ext ebnd'

    | Restrict face ->
      let face' = traverse_face face in
      Restrict face'

    | Cons (t0, t1) ->
      let t0' = traverse_tm t0 in
      let t1' = traverse_tm t1 in
      Cons (t0', t1')

    | V info ->
      let r = traverse_tm info.r in
      let ty0 = traverse_tm info.ty0 in
      let ty1 = traverse_tm info.ty1 in
      let equiv = traverse_tm info.equiv in
      V {r; ty0; ty1; equiv}

    | VIn info ->
      let r = traverse_tm info.r in
      let tm0 = traverse_tm info.tm0 in
      let tm1 = traverse_tm info.tm1 in
      VIn {r; tm0; tm1}

    | Lam bnd ->
      let bnd' = traverse_bnd traverse_tm bnd in
      Lam bnd'

    | ExtLam nbnd ->
      let nbnd' = traverse_nbnd traverse_tm nbnd in
      ExtLam nbnd'

    | RestrictThunk face ->
      let face' = traverse_face face in
      RestrictThunk face'

    | Box info ->
      let r = traverse_tm info.r in
      let r' = traverse_tm info.r' in
      let cap = traverse_tm info.cap in
      let sys = traverse_list traverse_face info.sys in
      Box {r; r'; cap; sys}

    | LblTy info ->
      let args = traverse_list (traverse_pair traverse_tm traverse_tm) info.args in
      let ty = traverse_tm info.ty in
      LblTy {info with args; ty}

    | LblRet t ->
      let t' = traverse_tm t in
      LblRet t'

    | Later bnd ->
      let bnd' = traverse_bnd traverse_tm bnd in
      Later bnd'

    | Next bnd ->
      let bnd' = traverse_bnd traverse_tm bnd in
      Next bnd'

    | Let (cmd, bnd) ->
      let cmd' = traverse_cmd cmd in
      let bnd' = traverse_bnd traverse_tm bnd in
      Let (cmd', bnd')

    | Up cmd ->
      let cmd' = traverse_cmd cmd in
      Up cmd'

    | Data lbl ->
      Data lbl

    | Intro (dlbl, clbl, args) ->
      let args' = traverse_list traverse_tm args in
      Intro (dlbl, clbl, args')


  and traverse_cmd (hd, sp) =
    let hd', sp' = traverse_head hd in
    let sp'' =
      match hd' with
      | Meta _ ->
        A.under_meta @@ fun _ -> traverse_spine sp
      | _ ->
        traverse_spine sp
    in
    hd', sp' <.> sp''

  and traverse_spine sp =
    traverse_bwd traverse_frame sp

  and traverse_head =
    function
    | Ix (ix, twin) ->
      A.bvar ~ih:traverse_cmd ~ix ~twin

    | Var {name; twin; ushift} ->
      A.fvar ~name ~twin ~ushift

    | Meta {name; ushift} ->
      A.meta ~name ~ushift

    | Down info ->
      let ty = traverse_tm info.ty in
      let tm = traverse_tm info.tm in
      Down {ty; tm}, Emp

    | DownX r ->
      DownX (traverse_tm r), Emp

    | DFix info ->
      let r = traverse_tm info.r in
      let ty = traverse_tm info.ty in
      let bdy = traverse_bnd traverse_tm info.bdy in
      DFix {r; ty; bdy}, Emp

    | Coe info ->
      let r = traverse_tm info.r in
      let r' = traverse_tm info.r' in
      let ty = traverse_bnd traverse_tm info.ty in
      let tm = traverse_tm info.tm in
      let coe = Coe {r; r'; ty; tm} in
      coe, Emp

    | HCom info ->
      let r = traverse_tm info.r in
      let r' = traverse_tm info.r' in
      let ty = traverse_tm info.ty in
      let cap = traverse_tm info.cap in
      let sys = traverse_list traverse_bface info.sys in
      let hcom = HCom {r; r'; ty; cap; sys} in
      hcom, Emp

    | GHCom info ->
      let r = traverse_tm info.r in
      let r' = traverse_tm info.r' in
      let ty = traverse_tm info.ty in
      let cap = traverse_tm info.cap in
      let sys = traverse_list traverse_bface info.sys in
      let hcom = GHCom {r; r'; ty; cap; sys} in
      hcom, Emp

    | Com info ->
      let r = traverse_tm info.r in
      let r' = traverse_tm info.r' in
      let ty = traverse_bnd traverse_tm info.ty in
      let cap = traverse_tm info.cap in
      let sys = traverse_list traverse_bface info.sys in
      let com = Com {r; r'; ty; cap; sys} in
      com, Emp

    | GCom info ->
      let r = traverse_tm info.r in
      let r' = traverse_tm info.r' in
      let ty = traverse_bnd traverse_tm info.ty in
      let cap = traverse_tm info.cap in
      let sys = traverse_list traverse_bface info.sys in
      let com = GCom {r; r'; ty; cap; sys} in
      com, Emp

  and traverse_bnd : 'a. ('a -> 'b) -> 'a bnd -> 'b bnd =
    fun f (B (nm, tm)) ->
      let tm' = A.with_bindings 1 (fun _ -> f tm) in
      B (nm, tm')

  and traverse_nbnd : 'a 'b. ('a -> 'b) -> 'a nbnd -> 'b nbnd =
    fun f (NB (nms, tm)) ->
      let tm' = A.with_bindings (Bwd.length nms) (fun _ -> f tm) in
      NB (nms, tm')

  and traverse_bface (r, r', obnd) =
    let s = traverse_tm r in
    let s' = traverse_tm r' in
    let obnd' = traverse_opt (traverse_bnd traverse_tm) obnd in
    s, s', obnd'

  and traverse_face (r, r', otm) =
    let s = traverse_tm r in
    let s' = traverse_tm r' in
    let otm' = traverse_opt traverse_tm otm in
    s, s', otm'

  and traverse_pair : 'a 'b 'c 'd. ('a -> 'c) -> ('b -> 'd) -> 'a * 'b -> ('c * 'd) =
    fun f g (a, b) ->
      let c = f a in
      let d = g b in
      c, d

  and traverse_opt : 'a 'b. ('a -> 'b) -> 'a option -> 'b option =
    fun f ->
      function
      | None ->
        None
      | Some a ->
        let a' = f a in
        Some a'

  and traverse_list : 'a 'b. ('a -> 'b) -> 'a list -> 'b list =
    fun f ->
      function
      | [] -> []
      | x :: xs ->
        let x' = f x in
        let xs' = traverse_list f xs in
        x' :: xs'

  and traverse_bwd : 'a 'b. ('a -> 'b) -> 'a bwd -> 'b bwd =
    fun f ->
      function
      | Emp -> Emp
      | Snoc (xs, x) ->
        let xs' = traverse_bwd f xs in
        let x' = f x in
        Snoc (xs', x')


  and traverse_frame =
    function
    | (Car | Cdr | LblCall | RestrictForce as frm) ->
      frm

    | FunApp t ->
      let t' = traverse_tm t in
      FunApp t'

    | ExtApp ts ->
      let ts' = traverse_list traverse_tm ts in
      ExtApp ts'

    | Elim info ->
      let mot = traverse_bnd traverse_tm info.mot in
      let clauses = List.map (fun (lbl, bnd) -> lbl, traverse_nbnd traverse_tm bnd) info.clauses in
      Elim {info with mot; clauses}

    | VProj info ->
      let r = traverse_tm info.r in
      let func = traverse_tm info.func in
      VProj {r; func}

    | Cap info ->
      let r = traverse_tm info.r in
      let r' = traverse_tm info.r' in
      let ty = traverse_tm info.ty in
      let sys = traverse_list traverse_bface info.sys in
      Cap {r; r'; ty; sys}

    | Prev tick ->
      let tick = traverse_tm tick in
      Prev tick

end














module SubstAlg (Init : sig val subst : tm cmd subst end) :
sig
  include Alg
end =
struct

  let subst = ref Init.subst

  let should_traverse info =
    not @@ Info.is_locally_closed info

  let rec lift sub =
    Dot (ix 0, Cmp (Shift 1, sub))

  and liftn n (sub : tm cmd subst) : tm cmd subst  =
    match n with
    | 0 -> sub
    | _ -> liftn (n - 1) @@ lift sub

  let under_meta f = f ()

  let with_bindings n f =
    let old = !subst in
    subst := liftn n old;
    let r = f () in
    subst := old;
    r

  let rec bvar ~ih ~ix ~twin =
    match !subst, ix with
    | Shift n, _ ->
      Ix (ix + n, twin), Emp

    | Dot (cmd, _), 0 ->
      cmd

    | Dot (_, sub), _ ->
      let old = !subst in
      subst := sub;
      let r = bvar ~ih ~ix:(ix - 1) ~twin in
      subst := old;
      r

    | Cmp (sub1, sub0), _ ->
      subst := cmp_subst ih sub1 sub0;
      bvar ~ih ~ix ~twin


  and cmp_subst ih sub0 sub1 =
    match sub0, sub1 with
    | s, Shift 0 ->
      s
    | Dot (_, sub0), Shift m ->
      cmp_subst ih sub0 (Shift (m - 1))
    | Shift m, Shift n ->
      Shift (m + n)
    | sub0, Dot (e, sub1) ->
      let old = !subst in
      subst := sub0;
      let e' = ih e in
      subst := old;
      let sub' = cmp_subst ih sub0 sub1 in
      Dot (e', sub')
    | Cmp (sub0, sub1), sub ->
      let sub' = cmp_subst ih sub0 sub1 in
      cmp_subst ih sub' sub
    | sub, Cmp (sub0, sub1) ->
      let sub' = cmp_subst ih sub0 sub1 in
      cmp_subst ih sub sub'

  let fvar ~name ~twin ~ushift =
    Var {name; twin; ushift}, Emp
  let meta ~name ~ushift =
    Meta {name; ushift}, Emp
end

let subst sub tm =
  let module Init = struct let subst = sub end in
  let module T = Traverse (SubstAlg (Init)) in
  T.traverse_tm tm

let subst_cmd sub cmd =
  let module Init = struct let subst = sub end in
  let module T = Traverse (SubstAlg (Init)) in
  T.traverse_cmd cmd

let unleash (Tm info) =
  info.con

module OpenVarAlg (Init : sig val twin : twin option val name : Name.t val ix : int end) : Alg =
struct
  let state = ref Init.ix

  let should_traverse info =
    not @@ Info.is_locally_closed info

  let with_bindings n f =
    let old = !state in
    state := old + n;
    let r = f () in
    state := old;
    r

  let under_meta f =
    f ()

  let bvar ~ih:_ ~ix ~twin =
    if ix = !state then
      let twin =
        match Init.twin with
        | None -> twin
        | Some twin -> twin
      in
      Var {name = Init.name; ushift = 0; twin}, Emp
    else
      Ix (ix, twin), Emp

  let fvar ~name ~twin ~ushift =
    Var {name; twin; ushift}, Emp

  let meta ~name ~ushift =
    Meta {name; ushift}, Emp
end

module CloseVarAlg (Init : sig val twin : twin option val name : Name.t val ix : int end) : Alg =
struct
  let state = ref Init.ix

  let should_traverse _ = true

  let under_meta f = f ()

  let with_bindings k f =
    let old = !state in
    state := old + k;
    let r = f () in
    state := old;
    r

  let bvar ~ih:_ ~ix ~twin =
    Ix (ix, twin), Emp

  let fvar ~name ~twin ~ushift =
    if name = Init.name then
      Ix (!state, match Init.twin with None -> twin | Some twin -> twin), Emp
    else
      Var {name; twin; ushift}, Emp


  let meta ~name ~ushift =
    Meta {name; ushift}, Emp
end


let open_var k ?twin:(twin = None) x tm =
  let module Init =
  struct
    let name = x
    let twin = twin
    let ix = k
  end
  in
  let module T = Traverse (OpenVarAlg (Init)) in
  T.traverse_tm tm


let close_var a ?twin:(twin = None) k tm =
  let module Init =
  struct
    let twin = twin
    let name = a
    let ix = k
  end
  in
  let module T = Traverse (CloseVarAlg (Init)) in
  let res = T.traverse_tm tm in
  res

let unbind (B (nm, t)) =
  let x = Name.named nm in
  x, open_var 0 x t

let unbind_with cmd (B (_, t)) =
  let sb = dot cmd @@ shift 0 in
  subst sb t

let unbindn (NB (nms, t)) =
  let rec go k nms xs t =
    match nms with
    | Emp -> Bwd.from_list xs, t
    | Snoc (nms, nm) ->
      let x = Name.named nm in
      go (k + 1) nms (x :: xs) @@ open_var k x t
  in
  go 0 nms [] t


let map_tm_face f (r, r', otm) =
  f r, f r', Option.map f otm

let map_tm_sys f =
  List.map @@ map_tm_face f

let unbind_ext (NB (nms, (ty, sys))) =
  let n = Bwd.length nms in
  let rec go k nms xs ty sys =
    match nms with
    | Emp -> Bwd.from_list xs, ty, sys
    | Snoc (nms, nm)  ->
      let x = Name.named nm in
      go (k + 1) nms (x :: xs) (open_var (n - k - 1) x ty) (map_tm_sys (open_var (n - k - 1) x) sys)
  in
  go 0 nms [] ty sys

let unbind_ext_with rs ebnd =
  let NB (nms, (ty, sys)) = ebnd in
  let n = Bwd.length nms in

  let rec go acc =
    function
    | [] ->
      acc
    | r :: rs ->
      go (dot r acc) rs
  in

  let sb = go (shift 0) rs in
  if Bwd.length nms = List.length rs then
    subst sb ty, map_tm_sys (subst sb) sys
  else
    let err = UnbindExtLengthMismatch (rs, ebnd) in
    raise @@ E err

let unbindn_with cmds nbnd =
  let NB (nms, tm) = nbnd in
  let n = Bwd.length nms in

  let rec go acc =
    function
    | [] ->
      acc
    | cmd :: cmds ->
      go (dot cmd acc) cmds
  in

  let sb = go (shift 0) cmds in
  if Bwd.length nms = List.length cmds then
    subst sb tm
  else
    let err = UnbindLengthMismatch (cmds, nbnd) in
    raise @@ E err

let bind x tx =
  B (Name.name x, close_var x 0 tx)

let bindn xs txs =
  let rec go k xs txs =
    match xs with
    | Emp -> txs
    | Snoc (xs, x) ->
      go (k + 1) xs @@ close_var x k txs
  in
  NB (Bwd.map Name.name xs, go 0 xs txs)

let bind_ext xs tyxs sysxs =
  let rec go k xs tyxs sysxs =
    match xs with
    | Emp -> tyxs, sysxs
    | Snoc (xs, x) ->
      go (k + 1) xs (close_var x k tyxs) (map_tm_sys (close_var x k) sysxs)
  in
  NB (Bwd.map Name.name xs, go 0 xs tyxs sysxs)

let rec pp env fmt =
  let rec go env mode fmt t =
    match unleash t with
    | Pi (dom, B (nm, cod)) ->
      let x, env' = Pp.Env.bind env nm  in
      if mode = `Pi then
        Format.fprintf fmt "[%a : %a]@ %a" Uuseg_string.pp_utf_8 x (pp env) dom (go env' `Pi) cod
      else
        Format.fprintf fmt "@[<hv1>(%a @[<hv>[%a : %a]@ %a@])@]" Uuseg_string.pp_utf_8 "→" Uuseg_string.pp_utf_8 x (pp env) dom (go env' `Pi) cod

    | Sg (dom, B (nm, cod)) ->
      let x, env' = Pp.Env.bind env nm in
      if mode = `Sg then
        Format.fprintf fmt "[%a : %a]@ %a" Uuseg_string.pp_utf_8 x (pp env) dom (go env' `Sg) cod
      else
        Format.fprintf fmt "@[<hv1>(%a @[<hv>[%a : %a]@ %a@])@]" Uuseg_string.pp_utf_8 "×" Uuseg_string.pp_utf_8 x (pp env) dom (go env' `Sg) cod

    | Ext (NB (nms, (cod, sys))) ->
      let xs, env' = Pp.Env.bindn env (Bwd.to_list nms) in
      begin
        match sys with
        | [] ->
          Format.fprintf fmt "@[<hv1>(# <%a>@ %a)@]" pp_strings xs (pp env') cod
        | _ ->
          Format.fprintf fmt "@[<hv1>(# @[<hv1><%a>@ %a@ @[<hv>%a@]@])@]" pp_strings xs (pp env') cod (pp_sys env') sys
      end

    | Restrict face ->
      Format.fprintf fmt "@[<hv1>(=>@ %a)@]" (pp_face env) face

    | V info ->
      Format.fprintf fmt "@[<hv1>(V %a@ %a@ %a@ %a)@]" (pp env) info.r (pp env) info.ty0 (pp env) info.ty1 (pp env) info.equiv

    | VIn info ->
      Format.fprintf fmt "@[<hv1>(Vin %a@ %a@ %a)@]" (pp env) info.r (pp env) info.tm0 (pp env) info.tm1

    | Lam (B (nm, tm)) ->
      let x, env' = Pp.Env.bind env nm in
      if mode = `Lam then
        Format.fprintf fmt "[%a]@ %a" Uuseg_string.pp_utf_8 x (go env' `Lam) tm
      else
        Format.fprintf fmt "@[<1>(λ [%a]@ %a)@]" Uuseg_string.pp_utf_8 x (go env' `Lam) tm

    | ExtLam (NB (nms, tm)) ->
      let xs, env' = Pp.Env.bindn env (Bwd.to_list nms) in
      if mode = `Lam then
        Format.fprintf fmt "<%a>@ %a" pp_strings xs (go env' `Lam) tm
      else
        Format.fprintf fmt "@[<hv1>(λ <%a>@ %a)@]" pp_strings xs (go env' `Lam) tm

    | RestrictThunk face ->
      pp_face env fmt face

    | Dim0 ->
      Format.fprintf fmt "0"

    | Dim1 ->
      Format.fprintf fmt "1"

    | Univ {kind; lvl} ->
      Format.fprintf fmt "(U %a %a)" Kind.pp kind Lvl.pp lvl

    | FHCom {r; r'; cap; sys} ->
      Format.fprintf fmt "@[<hv1>(fhcom %a %a@ %a@ @[%a@])@]" (pp env) r (pp env) r' (pp env) cap (pp_bsys env) sys

    | LblTy {lbl; args; ty} ->
      begin
        match args with
        | [] ->
          Format.fprintf fmt "@[<hv1>{%a : %a}@]"
            Uuseg_string.pp_utf_8 lbl
            (pp env) ty
        | _ ->
          Format.fprintf fmt "@[<hv1>{%a %a : %a}@]"
            Uuseg_string.pp_utf_8 lbl
            (pp_lbl_args env) args
            (pp env) ty
      end

    | LblRet t ->
      Format.fprintf fmt "@[<hv1>(ret@ %a)@]"
        (pp env) t

    | Cons (tm0, tm1) ->
      Format.fprintf fmt "@[<hv1>(pair@ %a@ %a)@]" (pp env) tm0 (pp env) tm1

    | Box {r; r'; cap; sys} ->
      Format.fprintf fmt "@[<hv1>(box %a %a@ %a@ @[<hv>%a@])@]" (pp env) r (pp env) r' (pp env) cap (pp_sys env) sys

    | Later (B (nm, t)) ->
      let x, env' = Pp.Env.bind env nm in
      Format.fprintf fmt "@[<hv1>(%a [%a]@ %a)@]" Uuseg_string.pp_utf_8 "▷" Uuseg_string.pp_utf_8 x (pp env') t

    | Next (B (nm, t)) ->
      let x, env' = Pp.Env.bind env nm in
      Format.fprintf fmt "@[<hv1>(next [%a]@ %a)@]" Uuseg_string.pp_utf_8 x (pp env') t

    | Let (cmd, B (nm, t)) ->
      let x, env' = Pp.Env.bind env nm in
      Format.fprintf fmt "@[<hv1>(let@ @[<hv1>[%a %a]@]@ %a)@]" Uuseg_string.pp_utf_8 x (pp_cmd env) cmd (pp env') t

    | Up cmd ->
      pp_cmd env fmt cmd

    | Data lbl ->
      Desc.pp_data_label fmt lbl

    | Intro (_dlbl, clbl, args) ->
      begin
        match args with
        | [] ->
          Desc.pp_con_label fmt clbl
        | _ ->
          Format.fprintf fmt "@[<hv1>(%a@ %a)@]"
            Desc.pp_con_label clbl
            (pp_terms env) args
      end

  in
  go env `Start fmt

and pp_head env fmt =
  function
  | Coe {r; r'; ty = B (nm, ty); tm} ->
    let x, env' = Pp.Env.bind env nm in
    Format.fprintf fmt "@[<hv1>(coe %a %a@ <%a> %a@ %a)@]" (pp env) r (pp env) r' Uuseg_string.pp_utf_8 x (pp env') ty (pp env) tm

  | HCom {r; r'; ty; cap; sys} ->
    Format.fprintf fmt "@[<hv1>(hcom %a %a@ %a@ %a@ @[%a@])@]" (pp env) r (pp env) r' (pp env) ty (pp env) cap (pp_bsys env) sys

  | Com {r; r'; ty = B (nm, ty); cap; sys} ->
    let x, env' = Pp.Env.bind env nm in
    Format.fprintf fmt "@[<hv1>(com %a %a@ [%a] %a@ %a@ @[%a@])@]" (pp env) r (pp env) r' Uuseg_string.pp_utf_8 x (pp env') ty (pp env) cap (pp_bsys env) sys

  | GHCom {r; r'; ty; cap; sys} ->
    Format.fprintf fmt "@[<hv1>(ghcom %a %a@ %a@ %a@ @[%a@])@]" (pp env) r (pp env) r' (pp env) ty (pp env) cap (pp_bsys env) sys

  | GCom {r; r'; ty = B (nm, ty); cap; sys} ->
    let x, env' = Pp.Env.bind env nm in
    Format.fprintf fmt "@[<hv1>(gcom %a %a@ [%a] %a@ %a@ @[%a@])@]" (pp env) r (pp env) r' Uuseg_string.pp_utf_8 x (pp env') ty (pp env) cap (pp_bsys env) sys

  | Ix (ix, _tw) ->
    (* Format.fprintf fmt "#%i/" ix; *)
    Uuseg_string.pp_utf_8 fmt @@
    Pp.Env.var ix env

  | Var info ->
    Name.pp fmt info.name;
    if info.ushift > 0 then Format.fprintf fmt "^%i" info.ushift

  | Meta {name; ushift} when ushift = 0 ->
    Name.pp fmt name

  | Meta {name; ushift} ->
    Format.fprintf fmt "%a^%i"
      Name.pp name
      ushift

  | Down {ty; tm} ->
    Format.fprintf fmt "@[<hv1>(: @[<hov>%a@ %a@])@]" (pp env) ty (pp env) tm

  | DownX r ->
    pp env fmt r

  | DFix {r; ty; bdy = B (nm, bdy)} ->
    let x, env' = Pp.Env.bind env nm in
    Format.fprintf fmt "@[<hv1>(dfix %a %a@ [%a] %a)@]" (pp env) r (pp env) ty Uuseg_string.pp_utf_8 x (pp env') bdy

and pp_cmd env fmt (hd, sp) =
  let rec go mode fmt sp =
    match sp with
    | Emp -> pp_head env fmt hd
    | Snoc (sp, f)->
      match f with
      | Car ->
        Format.fprintf fmt "@[<hv1>(fst %a)@]" (go `Car) sp
      | Cdr ->
        Format.fprintf fmt "@[<hv1>(snd %a)@]" (go `Car) sp
      | FunApp t ->
        if mode = `FunApp then
          Format.fprintf fmt "%a@ %a" (go `FunApp) sp (pp env) t
        else
          Format.fprintf fmt "@[<hv1>(%a@ %a)@]" (go `FunApp) sp (pp env) t
      | ExtApp ts ->
        begin
          match ts with
          | [] ->
            Format.fprintf fmt "@[<hv1>(%s %a)@]" "@" (go `ExtApp) sp
          | _ ->
            Format.fprintf fmt "@[<hv1>(%s %a@ %a)@]" "@" (go `ExtApp) sp (pp_terms env) ts
        end
      | Elim info ->
        let B (nm_mot, mot) = info.mot in
        let x_mot, env_mot = Pp.Env.bind env nm_mot in
        (* TODO *)
        Format.fprintf fmt "@[<hv1>(%a.elim@ [%a] %a@ %a@ %a)@]"
          Desc.pp_data_label info.dlbl
          Uuseg_string.pp_utf_8 x_mot
          (pp env_mot) mot
          (go `Elim) sp
          (pp_elim_clauses env) info.clauses

      | VProj {r; func} ->
        Format.fprintf fmt "@[<hv1>(vproj %a@ %a@ %a)@]" (pp env) r (go `VProj) sp (pp env) func
      | Cap _ ->
        (* FIXME *)
        Format.fprintf fmt "@<cap>"
      | LblCall ->
        Format.fprintf fmt "@[<hv1>(call@ %a)@]" (go `Call) sp
      | RestrictForce ->
        Format.fprintf fmt "@[<hv1>(force@ %a)@]" (go `Force) sp
      | Prev tick ->
        Format.fprintf fmt "@[<hv1>(prev %a@ %a)@]" (pp env) tick (go `Prev) sp
  in
  go `Start fmt sp

and pp_elim_clauses env fmt clauses =
  let pp_sep fmt () = Format.fprintf fmt "@ " in
  Format.pp_print_list ~pp_sep (pp_elim_clause env) fmt clauses

and pp_elim_clause env fmt (clbl, nbnd) =
  Format.fprintf fmt "@[<hv1>(%a@ %a)@]"
    Desc.pp_con_label clbl
    (pp_nbnd env) nbnd

and pp_nbnd env fmt nbnd =
  let NB (nms, tm) = nbnd in
  match nms with
  | Emp ->
    pp env fmt tm
  | _ ->
    let xs, env' = Pp.Env.bindn env (Bwd.to_list nms) in
    Format.fprintf fmt "@[<hv1>[%a]@ %a@]" pp_strings xs (pp env') tm

and pp_bnd env fmt nbnd =
  let B (nm, tm) = nbnd in
  let x, env' = Pp.Env.bind env nm in
  Format.fprintf fmt "@[<hv1>[%s]@ %a@]" x (pp env') tm

and pp_spine env fmt sp =
  match sp with
  | Emp ->
    Format.fprintf fmt "[]"
  | Snoc (sp, f) ->
    Format.fprintf fmt "%a. %a"
      (pp_spine env) sp
      (pp_frame env) f

and pp_frame env fmt =
  function
  | FunApp t ->
    Format.fprintf fmt "@[<hv1>(app %a)@]" (pp env) t
  | ExtApp ts ->
    Format.fprintf fmt "@[<hv1>(ext-app %a)@]" (pp_terms env) ts
  | Car ->
    Format.fprintf fmt "car"
  | Cdr ->
    Format.fprintf fmt "cdr"
  | VProj _ ->
    Format.fprintf fmt "<vproj>"
  | Cap _ ->
    Format.fprintf fmt "<cap>"
  | LblCall ->
    Format.fprintf fmt "lblcall"
  | RestrictForce ->
    Format.fprintf fmt "restrict-force"
  | Prev _ ->
    Format.fprintf fmt "<prev>"
  | Elim info ->
    Format.fprintf fmt "@[<hv1>(%a.elim@ %a@ %a)@]"
      Desc.pp_data_label info.dlbl
      (pp_bnd env) info.mot
      (pp_elim_clauses env) info.clauses

and pp_lbl_args env fmt args =
  let pp_sep fmt () = Format.fprintf fmt " " in
  let pp_arg fmt (_, tm) = pp env fmt tm in
  Format.pp_print_list ~pp_sep pp_arg fmt args

and pp_terms env fmt ts =
  let pp_sep fmt () = Format.fprintf fmt "@ " in
  Format.pp_print_list ~pp_sep (pp env) fmt ts

and pp_strings fmt (xs : string list) : unit =
  let pp_sep fmt () = Format.fprintf fmt " " in
  Format.pp_print_list ~pp_sep Uuseg_string.pp_utf_8 fmt xs

and pp_sys env fmt sys =
  match sys with
  | [] ->
    ()

  | [face] ->
    pp_face env fmt face

  | face :: sys ->
    Format.fprintf fmt "%a@ %a" (pp_face env) face (pp_sys env) sys

and pp_bsys env fmt sys =
  match sys with
  | [] ->
    ()

  | [face] ->
    pp_bface env fmt face

  | face :: sys ->
    Format.fprintf fmt "%a@ %a" (pp_bface env) face (pp_bsys env) sys

and pp_face env fmt face =
  let r, r', otm = face in
  match otm with
  | None ->
    Format.fprintf fmt "@[<hv1>[%a=%a@ -]@]" (pp env) r (pp env) r'

  | Some tm ->
    Format.fprintf fmt "@[<hv1>[%a=%a@ %a]@]" (pp env) r (pp env) r' (pp env) tm

and pp_bface env fmt face =
  let r, r', obnd = face in
  match obnd with
  | None ->
    Format.fprintf fmt "@[<hv1>[%a=%a@ -]@]" (pp env) r (pp env) r'

  | Some (B (nm, tm)) ->
    let x, env' = Pp.Env.bind env nm in
    Format.fprintf fmt "@[<hv1>[%a=%a@ <%a> %a]@]" (pp env) r (pp env) r' Uuseg_string.pp_utf_8 x (pp env') tm


let up cmd = make @@ Up cmd

let ann ~ty ~tm =
  Down {ty; tm}, Emp

let car (hd, sp) =
  hd, sp #< Car

let cdr (hd, sp) =
  hd, sp #< Cdr

let lam nm t = make @@ Lam (B (nm, t))
let ext_lam nms t = make @@ ExtLam (NB (nms, t))
let pi nm dom cod = make @@ Pi (dom, B (nm, cod))
let sg nm dom cod = make @@ Sg (dom, B (nm, cod))
let let_ nm t0 t1 = make @@ Let (t0, B (nm, t1))
let cons t0 t1 = make @@ Cons (t0, t1)
let univ ~kind ~lvl = make @@ Univ {kind; lvl}


let arr ty0 ty1 =
  pi None ty0 @@
  subst (Shift 1) ty1

let times ty0 ty1 =
  sg None ty0 @@
  subst (Shift 1) ty1

let path ty tm0 tm1 =
  let ty' = subst (Shift 1) ty in
  let face0 = up (ix 0), make Dim0, Some (subst (Shift 1) tm0) in
  let face1 = up (ix 0), make Dim1, Some (subst (Shift 1) tm1) in
  let sys = [face0; face1] in
  make @@ Ext (NB (Emp #< None, (ty', sys)))

let fiber ~ty0 ~ty1 ~f ~x =
  sg (Some "ix") ty0 @@
  let app =
    Down {tm = subst (Shift 1) f; ty = arr ty0 ty1},
    (Emp #< (FunApp (up (ix 0))))
  in
  path
    (subst (Shift 1) ty1)
    (up app)
    (subst (Shift 1) x)

let proj2 = Shift 2

let is_contr ty =
  sg (Some "center") ty @@
  pi (Some "other") (subst (Shift 1) ty) @@
  path
    (subst proj2 ty)
    (up @@ ix 0)
    (up @@ ix 1)

let equiv ty0 ty1 =
  sg (Some "fun") (arr ty0 ty1) @@
  pi (Some "el") (subst (Shift 1) ty1) @@
  is_contr @@
  fiber
    ~ty0:(subst proj2 ty0)
    ~ty1:(subst proj2 ty1)
    ~f:(up @@ ix 1)
    ~x:(up @@ ix 0)


let refine_ty ty sys =
  let ebnd = NB (Emp, (ty, sys)) in
  make @@ Ext ebnd

let refine_thunk tm =
  make @@ ExtLam (NB (Emp, tm))

let refine_force (hd, sp) =
  hd, sp #< (ExtApp [])


module OccursAlg (Init : sig val fl : Occurs.flavor end) :
sig
  include Alg
  val get : unit -> Occurs.Set.t
end =
struct
  let should_traverse _ = true

  let state = ref Occurs.Set.empty
  let srigid = ref true
  let get () = !state

  open Init

  let insert x =
    state := Occurs.Set.add x !state

  let with_bindings _ f =
    f ()


  let under_meta f =
    let old = !srigid in
    srigid := false;
    let r = f () in
    srigid := old;
    r


  let bvar ~ih:_ ~ix ~twin =
    Ix (ix, twin), Emp

  let fvar ~name ~twin ~ushift =
    begin
      if fl = `Vars || (fl = `RigVars && !srigid) then
        insert name
    end;
    Var {name; twin; ushift}, Emp

  let meta ~name ~ushift =
    begin
      if fl = `Metas then
        insert name
    end;
    Meta {name; ushift}, Emp
end




let free fl tm =
  let module Init = struct let fl = fl end in
  let module A = OccursAlg (Init) in
  let module T = Traverse (A) in
  let _ = T.traverse_tm tm in
  A.get ()


module Sp =
struct
  type t = tm spine
  let free fl sp =
    let module Init = struct let fl = fl end in
    let module A = OccursAlg (Init) in
    let module T = Traverse (A) in
    let _ = T.traverse_spine sp in
    A.get ()
end


let map_bnd (f : tm -> tm) (bnd : tm bnd) : tm bnd =
  let x, tx = unbind bnd in
  bind x @@ f tx

(* TODO: clean up *)
let map_nbnd (f : tm -> tm) (nbnd : tm nbnd) : tm nbnd =
  let xs, txs = unbindn nbnd in
  bindn xs @@ f txs


let map_comp_face f (r, r', obnd) =
  f r, f r', Option.map (map_bnd f) obnd

let map_comp_sys f =
  List.map @@ map_comp_face f

let map_head f =
  function
  | Var info -> Var info
  | Meta a -> Meta a
  | Ix (i, tw) -> Ix (i, tw)
  | Down info ->
    let ty = f info.ty in
    let tm = f info.tm in
    Down {ty; tm}
  | DownX r ->
    DownX (f r)
  | DFix info ->
    let r = f info.r in
    let ty = f info.ty in
    let bdy = map_bnd f info.bdy in
    DFix {r; ty; bdy}
  | Coe info ->
    let r = f info.r in
    let r' = f info.r' in
    let ty = map_bnd f info.ty in
    let tm = f info.tm in
    Coe {r; r'; ty; tm}
  | HCom info ->
    let r = f info.r in
    let r' = f info.r' in
    let ty = f info.ty in
    let cap = f info.cap in
    let sys = map_comp_sys f info.sys in
    HCom {r; r'; ty; cap; sys}
  | Com info ->
    let r = f info.r in
    let r' = f info.r' in
    let ty = map_bnd f info.ty in
    let cap = f info.cap in
    let sys = map_comp_sys f info.sys in
    Com {r; r'; ty; cap; sys}
  | GHCom info ->
    let r = f info.r in
    let r' = f info.r' in
    let ty = f info.ty in
    let cap = f info.cap in
    let sys = map_comp_sys f info.sys in
    GHCom {r; r'; ty; cap; sys}
  | GCom info ->
    let r = f info.r in
    let r' = f info.r' in
    let ty = map_bnd f info.ty in
    let cap = f info.cap in
    let sys = map_comp_sys f info.sys in
    GCom {r; r'; ty; cap; sys}

let map_frame f =
  function
  | (Car | Cdr | LblCall | RestrictForce) as frm ->
    frm
  | FunApp t ->
    FunApp (f t)
  | ExtApp ts ->
    ExtApp (List.map f ts)
  | Elim info ->
    let mot = map_bnd f info.mot in
    let clauses = List.map (fun (lbl, bnd) -> lbl, map_nbnd f bnd) info.clauses in
    Elim {info with mot; clauses}
  | VProj info ->
    let r = f info.r in
    let func = f info.func in
    VProj {r; func}
  | Cap info ->
    let r = f info.r in
    let r' = f info.r' in
    let ty = f info.ty in
    let sys = map_comp_sys f info.sys in
    Cap {r; r'; ty; sys}
  | Prev tick ->
    let tick = f tick in
    Prev tick

let map_spine f =
  Bwd.map @@ map_frame f


(* TODO: clean up: this is catastrophically bad *)
let rec map_ext_bnd f nbnd =
  match nbnd with
  | NB (Emp, (ty, sys)) ->
    NB (Emp, (f ty, map_tm_sys f sys))
  | NB (Snoc (nms, nm), (ty, sys)) ->
    let x = Name.named nm in
    let tyx = open_var 0 x ty in
    let sysx = map_tm_sys (open_var 0 x) sys in
    let NB (_, (tyx', sysx')) = map_ext_bnd f (NB (nms, (tyx, sysx))) in
    NB (nms #< nm, (close_var x 0 tyx', map_tm_sys (close_var x 0) sysx'))

let map_cmd f (hd, sp) =
  map_head f hd, map_spine f sp

let map_tmf f =
  function
  | (Univ _ | Dim0 | Dim1 | Data _) as con ->
    con
  | Cons (t0, t1) ->
    Cons (f t0, f t1)
  | LblRet t ->
    LblRet (f t)
  | FHCom info ->
    let r = f info.r in
    let r' = f info.r' in
    let cap = f info.cap in
    let sys = map_comp_sys f info.sys in
    FHCom {r; r'; cap; sys}
  | Pi (dom, cod) ->
    Pi (f dom, map_bnd f cod)
  | Sg (dom, cod) ->
    Sg (f dom, map_bnd f cod)
  | Ext ebnd ->
    Ext (map_ext_bnd f ebnd)
  | Restrict face ->
    Restrict (map_tm_face f face)
  | V info ->
    let r = f info.r in
    let ty0 = f info.ty0 in
    let ty1 = f info.ty1 in
    let equiv = f info.equiv in
    V {r; ty0; ty1; equiv}
  | VIn info ->
    let r = f info.r in
    let tm0 = f info.tm0 in
    let tm1 = f info.tm1 in
    VIn {r; tm0; tm1}
  | Lam bnd ->
    Lam (map_bnd f bnd)
  | ExtLam nbnd ->
    ExtLam (map_nbnd f nbnd)
  | RestrictThunk face ->
    RestrictThunk (map_tm_face f face)
  | Box info ->
    let r = f info.r in
    let r' = f info.r' in
    let cap = f info.cap in
    let sys = map_tm_sys f info.sys in
    Box {r; r'; cap; sys}
  | LblTy info ->
    let ty = f info.ty in
    let args = List.map (fun (t0, t1) -> f t0, f t1) info.args in
    LblTy {info with ty; args}
  | Later bnd ->
    let bnd = map_bnd f bnd in
    Later bnd
  | Next bnd ->
    let bnd = map_bnd f bnd in
    Next bnd
  | Up cmd ->
    Up (map_cmd f cmd)
  | Let (cmd, bnd) ->
    Let (map_cmd f cmd, map_bnd f bnd)
  | Intro (dlbl, clbl, args) ->
    Intro (dlbl, clbl, List.map f args)



let rec opt_traverse f xs =
  match xs with
  | [] -> Some []
  | x::xs ->
    match f x with
    | Some y -> Option.map (fun ys -> y :: ys) @@ opt_traverse f xs
    | None -> None


let as_plain_var t =
  match unleash t with
  | Up (Var {name; _}, Emp) ->
    Some name
  | _ ->
    None

(* A very crappy eta contraction function. It's horrific that this is actually a thing that we do! *)
let rec eta_contract t =
  match unleash t with
  | Lam bnd ->
    let y, tmy = unbind bnd in
    let tm'y = eta_contract tmy in
    begin
      match unleash tm'y with
      | Up (hd, Snoc (sp, FunApp arg)) ->
        begin
          match as_plain_var arg with
          | Some y'
            when
              y = y'
              && not @@ Occurs.Set.mem y @@ Sp.free `Vars sp
            ->
            up (hd, sp)
          | _ ->
            make @@ Lam (bind y tm'y)
        end
      | _ ->
        make @@ Lam (bind y tm'y)
    end

  | Next bnd ->
    let y, tmy = unbind bnd in
    let tm'y = eta_contract tmy in
    begin
      match unleash tm'y with
      | Up (hd, Snoc (sp, Prev arg)) ->
        begin
          match as_plain_var arg with
          | Some y'
            when
              y = y'
              && not @@ Occurs.Set.mem y @@ Sp.free `Vars sp
            ->
            up (hd, sp)
          | _ ->
            make @@ Next (bind y tm'y)
        end
      | _ ->
        make @@ Next (bind y tm'y)
    end

  | ExtLam nbnd ->
    let ys, tmys = unbindn nbnd in
    let tm'ys = eta_contract tmys in
    begin
      match unleash tm'ys with
      | Up (hd, Snoc (sp, ExtApp args)) ->
        begin
          match opt_traverse as_plain_var args with
          | Some y's
            when Bwd.to_list ys = y's
            (* TODO: && not @@ Occurs.Set.mem 'ys' @@ Tm.Sp.free `Vars sp *)
            ->
            up (hd, sp)
          | _ ->
            make @@ ExtLam (bindn ys tm'ys)
        end
      | _ ->
        make @@ ExtLam (bindn ys tm'ys)
    end

  | Cons (tm0, tm1) ->
    let tm0' = eta_contract tm0 in
    let tm1' = eta_contract tm1 in
    begin
      match unleash tm0', unleash tm1' with
      | Up (hd0, Snoc (sp0, Car)), Up (hd1, Snoc (sp1, Cdr))
        when
          hd0 = hd1 && sp0 = sp1
        ->
        up (hd0, sp0)

      | _ ->
        make @@ Cons (tm0', tm1')
    end

  | con ->
    make @@ map_tmf eta_contract con


let rec shift_univ k tm =
  if k = 0 then tm else
    match unleash tm with
    | Univ {lvl; kind} ->
      make @@ Univ {lvl = Lvl.shift k lvl; kind}
    | Up (Var info, sp) ->
      let hd' = Var {info with ushift = info.ushift + k} in
      let sp' = map_spine (shift_univ k) sp in
      make @@ Up (hd', sp')
    | Up (Meta {name; ushift}, sp) ->
      let hd' = Meta {name; ushift = ushift + k} in
      let sp' = map_spine (shift_univ k) sp in
      make @@ Up (hd', sp')
    | tmf ->
      make @@ map_tmf (shift_univ k) tmf

let pp0 fmt tm = pp Pp.Env.emp fmt @@ eta_contract tm

let rec pp_bterm fmt =
  let module B = Desc.Boundary in
  function
  | B.Var ix ->
    Format.fprintf fmt "#%i" ix
  | B.Intro intro ->
    Format.fprintf fmt "<intro: %s | %a | %a | %a>" intro.clbl (Pp.pp_list pp0) intro.const_args (Pp.pp_list pp_bterm) intro.rec_args (Pp.pp_list pp0) intro.rs


module Notation =
struct
  let (@<) cmd frm =
    let hd, sp = cmd in
    hd, sp #< frm
end

module Error =
struct
  type t = error
  exception E = E

  let pp fmt =
    function
    | InvalidDeBruijnIndex i ->
      Format.fprintf fmt
        "Tried to construct term with negative de bruijn index %i." i
    | UnbindExtLengthMismatch (_xs, _ebnd) ->
      Format.fprintf fmt
        "Tried to unbind extension type binder with incorrect number of variables."
    | UnbindLengthMismatch (_xs, _) ->
      Format.fprintf fmt
        "Tried to unbind n-ary tbinder with incorrect number of variables."

  let _ =
    PpExn.install_printer @@ fun fmt ->
    function
    | E err ->
      pp fmt err
    | _ ->
      raise PpExn.Unrecognized

end
