open RedBasis
open Bwd
open BwdNotation

type twin = [`Only | `TwinL | `TwinR]

type 'a bnd = B of string option * 'a
type 'a nbnd = NB of string option list * 'a

type info = Lexing.position * Lexing.position

type ('r, 'a) face = 'r * 'r * 'a option
type ('r, 'a) system = ('r, 'a) face list

type 'a tmf =
  | FCom of {r : 'a; r' : 'a; cap : 'a; sys : ('a, 'a bnd) system}

  | Univ of {kind : Kind.t; lvl : Lvl.t}
  | Pi of 'a * 'a bnd
  | Ext of ('a * ('a, 'a) system) nbnd
  | Rst of {ty : 'a; sys : ('a, 'a) system}
  | CoR of ('a, 'a) face
  | Sg of 'a * 'a bnd

  | V of {r : 'a; ty0 : 'a; ty1 : 'a; equiv : 'a}
  | VIn of {r : 'a; tm0 : 'a; tm1 : 'a}

  | Bool
  | Tt
  | Ff

  | Nat
  | Zero
  | Suc of 'a

  | Int
  | Pos of 'a
  | NegSuc of 'a

  | S1
  | Base
  | Loop of 'a

  | Lam of 'a bnd
  | ExtLam of 'a nbnd
  | CoRThunk of ('a, 'a) face

  | Cons of 'a * 'a
  | Dim0
  | Dim1

  | Box of {r : 'a; r' : 'a; cap : 'a; sys : ('a, 'a) system}

  (* Labelled types from Epigram *)
  | LblTy of {lbl : string; args : ('a * 'a) list; ty : 'a}
  | LblRet of 'a

  | Up of 'a cmd
  | Let of 'a cmd * 'a bnd

and 'a head =
  | Meta of {name: Name.t; ushift : int}
  | Ref of {name : Name.t; twin : twin; ushift : int}
  | Ix of int * twin
  | Down of {ty : 'a; tm : 'a}
  | Coe of {r : 'a; r' : 'a; ty : 'a bnd; tm : 'a}
  | HCom of {r : 'a; r' : 'a; ty : 'a; cap : 'a; sys : ('a, 'a bnd) system}
  | Com of {r : 'a; r' : 'a; ty : 'a bnd; cap : 'a; sys : ('a, 'a bnd) system}
  | GHCom of {r : 'a; r' : 'a; ty : 'a; cap : 'a; sys : ('a, 'a bnd) system}
  | GCom of {r : 'a; r' : 'a; ty : 'a bnd; cap : 'a; sys : ('a, 'a bnd) system}


and 'a frame =
  | Car
  | Cdr
  | FunApp of 'a
  | ExtApp of 'a list
  | If of {mot : 'a bnd; tcase : 'a; fcase : 'a}
  | S1Rec of {mot : 'a bnd; bcase : 'a; lcase : 'a bnd}
  | VProj of {r : 'a; ty0 : 'a; ty1 : 'a; equiv : 'a}
  | Cap of {r : 'a; r' : 'a; ty : 'a; sys : ('a, 'a bnd) system}
  | LblCall
  | CoRForce

and 'a spine = 'a frame bwd
and 'a cmd = 'a head * 'a spine

type tm = Tm of tm tmf

type 'a subst =
  | Shift of int
  | Dot of 'a * 'a subst

let ix ?twin:(tw = `Only) i =
  Ix (i, tw), Emp

let var ?twin:(tw = `Only) a =
  Ref {name = a; twin = tw; ushift = 0}, Emp


let rec cmp_subst sub0 sub1 =
  match sub0, sub1 with
  | s, Shift 0 -> s
  | Dot (_, sub0), Shift m -> cmp_subst sub0 (Shift (m - 1))
  | Shift m, Shift n -> Shift (m + n)
  | sub0, Dot (e, sub1) -> Dot (subst_cmd sub0 e, cmp_subst sub0 sub1)

and lift sub =
  Dot (ix 0, cmp_subst (Shift 1) sub)

and liftn n sub =
  match n with
  | 0 -> sub
  | _ -> liftn (n - 1) @@ lift sub

and subst (sub : tm cmd subst) (Tm con) =
  Tm (subst_f sub con)

and subst_f (sub : tm cmd subst) =
  function
  | (Dim0 | Dim1 | Univ _ | Bool | Tt | Ff | Nat | Zero | Int | S1 | Base) as con ->
    con

  | Suc n -> Suc (subst sub n)

  | Pos n -> Pos (subst sub n)
  | NegSuc n -> NegSuc (subst sub n)

  | Loop r -> Loop (subst sub r)

  | FCom info ->
    let r = subst sub info.r in
    let r' = subst sub info.r' in
    let cap = subst sub info.cap in
    let sys = subst_comp_sys sub info.sys in
    FCom {r; r'; cap; sys}

  | Up cmd ->
    Up (subst_cmd sub cmd)

  | Pi (dom, cod) ->
    Pi (subst sub dom, subst_bnd sub cod)

  | Sg (dom, cod) ->
    Sg (subst sub dom, subst_bnd sub cod)

  | Ext ebnd ->
    Ext (subst_ext_bnd sub ebnd)

  | Rst info ->
    let ty = subst sub info.ty in
    let sys = subst_tm_sys sub info.sys in
    Rst {ty; sys}

  | CoR face ->
    CoR (subst_tm_face sub face)

  | V info ->
    let r = subst sub info.r in
    let ty0 = subst sub info.ty0 in
    let ty1 = subst sub info.ty1 in
    let equiv = subst sub info.equiv in
    V {r; ty0; ty1; equiv}

  | VIn info ->
    let r = subst sub info.r in
    let tm0 = subst sub info.tm0 in
    let tm1 = subst sub info.tm1 in
    VIn {r; tm0; tm1}

  | Lam bnd ->
    Lam (subst_bnd sub bnd)

  | ExtLam nbnd ->
    ExtLam (subst_nbnd sub nbnd)

  | CoRThunk face ->
    CoRThunk (subst_tm_face sub face)

  | Cons (t0, t1) ->
    Cons (subst sub t0, subst sub t1)

  | Box info ->
    let r = subst sub info.r in
    let r' = subst sub info.r' in
    let cap = subst sub info.cap in
    let sys = subst_tm_sys sub info.sys in
    Box {r; r'; cap; sys}

  | LblTy info ->
    let args = List.map (fun (ty, tm) -> subst sub ty, subst sub tm) info.args in
    let ty = subst sub info.ty in
    LblTy {info with args; ty}

  | LblRet t ->
    LblRet (subst sub t)

  | Let (cmd, bnd) ->
    Let (subst_cmd sub cmd, subst_bnd sub bnd)

and subst_tm_sys sub  =
  List.map (subst_tm_face sub)

and subst_tm_face sub (r, r', otm) =
  subst sub r, subst sub r', Option.map (subst sub) otm


and subst_cmd sub (head, spine) =
  let head', spine' = subst_head sub head in
  let spine'' = subst_spine sub spine in
  head', spine' <.> spine''

and subst_spine sub spine =
  Bwd.map (subst_frame sub) spine

and subst_frame sub frame =
  match frame with
  | (Car | Cdr | LblCall | CoRForce) ->
    frame
  | FunApp t ->
    FunApp (subst sub t)
  | ExtApp ts ->
    ExtApp (List.map (subst sub) ts)
  | If info ->
    let mot = subst_bnd sub info.mot in
    let tcase = subst sub info.tcase in
    let fcase = subst sub info.fcase in
    If {mot; tcase; fcase}
  | S1Rec info ->
    let mot = subst_bnd sub info.mot in
    let bcase = subst sub info.bcase in
    let lcase = subst_bnd sub info.lcase in
    S1Rec {mot; bcase; lcase}
  | VProj info ->
    let r = subst sub info.r in
    let ty0 = subst sub info.ty0 in
    let ty1 = subst sub info.ty1 in
    let equiv = subst sub info.equiv in
    VProj {r; ty0; ty1; equiv}
  | Cap info ->
    let r = subst sub info.r in
    let r' = subst sub info.r' in
    let ty = subst sub info.ty in
    let sys = subst_comp_sys sub info.sys in
    Cap {r; r'; ty; sys}

and subst_head sub head =
  match head with
  | Ix (i, tw) ->
    begin
      match sub, i with
      | Shift n, _ -> Ix (i + n, tw), Emp
      | Dot (e, _), 0 -> e
      | Dot (_, sub), _ -> subst_head sub @@ Ix (i - 1, tw)
    end

  | Ref info ->
    Ref info, Emp

  | Meta a ->
    Meta a, Emp

  | Down info ->
    let ty = subst sub info.ty in
    let tm = subst sub info.tm in
    Down {ty; tm}, Emp

  | HCom info ->
    let r = subst sub info.r in
    let r' = subst sub info.r' in
    let ty = subst sub info.ty in
    let cap = subst sub info.cap in
    let sys = subst_comp_sys sub info.sys in
    HCom {r; r'; ty; cap; sys}, Emp

  | Coe info ->
    let r = subst sub info.r in
    let r' = subst sub info.r' in
    let ty = subst_bnd sub info.ty in
    let tm = subst sub info.tm in
    Coe {r; r'; ty; tm}, Emp

  | Com info ->
    let r = subst sub info.r in
    let r' = subst sub info.r' in
    let ty = subst_bnd sub info.ty in
    let cap = subst sub info.cap in
    let sys = subst_comp_sys sub info.sys in
    Com {r; r'; ty; cap; sys}, Emp

  | GHCom info ->
    let r = subst sub info.r in
    let r' = subst sub info.r' in
    let ty = subst sub info.ty in
    let cap = subst sub info.cap in
    let sys = subst_comp_sys sub info.sys in
    GHCom {r; r'; ty; cap; sys}, Emp

  | GCom info ->
    let r = subst sub info.r in
    let r' = subst sub info.r' in
    let ty = subst_bnd sub info.ty in
    let cap = subst sub info.cap in
    let sys = subst_comp_sys sub info.sys in
    GCom {r; r'; ty; cap; sys}, Emp

and subst_bnd sub bnd =
  let B (nm, t) = bnd in
  B (nm, subst (lift sub) t)

and subst_nbnd sub bnd =
  let NB (nms, t) = bnd in
  NB (nms, subst (liftn (List.length nms) sub) t)

and subst_ext_bnd sub ebnd =
  let NB (nms, (ty, sys)) = ebnd in
  let sub' = liftn (List.length nms) sub in
  let ty' = subst sub' ty in
  let sys' = subst_tm_sys sub' sys in
  NB (nms, (ty', sys'))


and subst_ext_sys sub sys =
  List.map (subst_ext_face sub) sys

and subst_ext_face sub (r, r', otm) =
  let r = subst sub r in
  let r' = subst sub r' in
  let otm = Option.map (subst sub) otm in
  r, r', otm

and subst_comp_face sub (r, r', obnd) =
  let r = subst sub r in
  let r' = subst sub r' in
  let obnd = Option.map (subst_bnd sub) obnd in
  r, r', obnd

and subst_comp_sys sub sys =
  List.map (subst_comp_face sub) sys

let make con =
  match con with
  | Up (Ix (ix, _), _) when ix < 0 -> failwith "make: Ix with negative index, wtf!!"
  | _ -> Tm con

let unleash (Tm con) = con

let traverse ~f ~var ~ref =
  let rec go k =
    function
    | Univ info -> Univ info
    | Bool -> Bool
    | Tt -> Tt
    | Ff -> Ff
    | Nat -> Nat
    | Zero -> Zero
    | Suc n -> Suc (f k n)
    | Int -> Int
    | Pos n -> Pos (f k n)
    | NegSuc n -> NegSuc (f k n)
    | S1 -> S1
    | Base -> Base
    | Loop r -> Loop (f k r)
    | Dim0 -> Dim0
    | Dim1 -> Dim1
    | Lam bnd ->
      Lam (go_bnd k bnd)
    | Pi (dom, cod) ->
      Pi (f k dom, go_bnd k cod)
    | Sg (dom, cod) ->
      Sg (f k dom, go_bnd k cod)
    | Ext ebnd ->
      Ext (go_ext_bnd k ebnd)
    | Rst info ->
      let ty = f k info.ty in
      let sys = go_tm_sys k info.sys in
      Rst {ty; sys}
    | CoR face ->
      CoR (go_tm_face k face)
    | FCom info ->
      let r = f k info.r in
      let r' = f k info.r' in
      let cap = f k info.cap in
      let sys = go_comp_sys k info.sys in
      FCom {r; r'; cap; sys}
    | V info ->
      let r = f k info.r in
      let ty0 = f k info.ty0 in
      let ty1 = f k info.ty1 in
      let equiv = f k info.equiv in
      V {r; ty0; ty1; equiv}
    | VIn info ->
      let r = f k info.r in
      let tm0 = f k info.tm0 in
      let tm1 = f k info.tm1 in
      VIn {r; tm0; tm1}
    | ExtLam nbnd ->
      ExtLam (go_nbnd k nbnd)
    | CoRThunk face ->
      CoRThunk (go_tm_face k face)
    | Cons (t0, t1) ->
      Cons (f k t0, f k t1)
    | Box info ->
      let r = f k info.r in
      let r' = f k info.r' in
      let cap = f k info.cap in
      let sys = go_tm_sys k info.sys in
      Box {r; r'; cap; sys}
    | LblTy info ->
      let args = List.map (fun (t0, t1) -> f k t0, f k t1) info.args in
      let ty = f k info.ty in
      LblTy {info with args; ty}
    | LblRet t ->
      LblRet (f k t)
    | Up cmd ->
      Up (go_cmd k cmd)
    | Let (cmd, bnd) ->
      Let (go_cmd k cmd, go_bnd k bnd)

  (* TODO: not sure if this is backwards !!!! *)
  and go_cmd k (hd, sp) =
    let hd', sp' = go_hd k hd in
    let sp'' = go_spine k sp in
    hd', sp' <.> sp''

  and go_hd k =
    function
    | Ix (i, tw) ->
      var k i tw
    | Ref info ->
      ref k (info.name, info.twin, info.ushift)
    | Meta a ->
      Meta a, Emp
    | Down info ->
      let ty = f k info.ty in
      let tm = f k info.tm in
      Down {ty; tm}, Emp
    | Coe info ->
      let r = f k info.r in
      let r' = f k info.r' in
      let ty = go_bnd k info.ty in
      let tm = f k info.tm in
      Coe {r; r'; ty; tm}, Emp
    | HCom info ->
      let r = f k info.r in
      let r' = f k info.r' in
      let ty = f k info.ty in
      let cap = f k info.cap in
      let sys = go_comp_sys k info.sys in
      HCom {r; r'; ty; cap; sys}, Emp
    | Com info ->
      let r = f k info.r in
      let r' = f k info.r' in
      let ty = go_bnd k info.ty in
      let cap = f k info.cap in
      let sys = go_comp_sys k info.sys in
      Com {r; r'; ty; cap; sys}, Emp
    | GHCom info ->
      let r = f k info.r in
      let r' = f k info.r' in
      let ty = f k info.ty in
      let cap = f k info.cap in
      let sys = go_comp_sys k info.sys in
      GHCom {r; r'; ty; cap; sys}, Emp
    | GCom info ->
      let r = f k info.r in
      let r' = f k info.r' in
      let ty = go_bnd k info.ty in
      let cap = f k info.cap in
      let sys = go_comp_sys k info.sys in
      GCom {r; r'; ty; cap; sys}, Emp

  and go_spine k =
    Bwd.map (go_frm k)

  and go_frm k =
    function
    | (Car | Cdr | LblCall | CoRForce) as frm -> frm
    | FunApp t ->
      FunApp (f k t)
    | ExtApp ts ->
      ExtApp (List.map (f k) ts)
    | If info ->
      let mot = go_bnd k info.mot in
      let tcase = f k info.tcase in
      let fcase = f k info.fcase in
      If {mot; tcase; fcase}
    | S1Rec info ->
      let mot = go_bnd k info.mot in
      let bcase = f k info.bcase in
      let lcase = go_bnd k info.lcase in
      S1Rec {mot; bcase; lcase}
    | VProj info ->
      let r = f k info.r in
      let ty0 = f k info.ty0 in
      let ty1 = f k info.ty1 in
      let equiv = f k info.equiv in
      VProj {r; ty0; ty1; equiv}
    | Cap info ->
      let r = f k info.r in
      let r' = f k info.r' in
      let ty = f k info.ty in
      let sys = go_comp_sys k info.sys in
      Cap {r; r'; ty; sys}


  and go_comp_sys k sys =
    List.map (go_comp_face k) sys

  and go_comp_face k (r, r', obnd) =
    f k r, f k r', Option.map (go_bnd k) obnd

  and go_ext_bnd k (NB (nms, (ty, sys))) =
    let k' = k + List.length nms in
    NB (nms, (f k' ty, go_tm_sys k' sys))

  and go_nbnd k (NB (nms, t)) =
    let k' = k + List.length nms in
    NB (nms, f k' t)

  and go_tm_sys k sys =
    List.map (go_tm_face k) sys

  and go_tm_face k (r, r', otm) =
    f k r, f k r', Option.map (f k) otm

  and go_bnd k : 'a bnd -> 'b bnd =
    function B (nm, t) ->
      B (nm, f (k + 1) t)

  in go

let fix_traverse ~var ~ref  =
  let rec go k (Tm tm) =
    Tm (traverse ~f:go ~var ~ref k tm)
  in
  go 0

let close_var a ?twin:(twin = fun _ -> `Only) k =
  let var _ i tw = Ix (i, tw), Emp in
  let ref n (b, tw, ush) =
    if b = a then
      ix ~twin:(twin tw) (n + k)
    else
      Ref {name = b; twin = tw; ushift = ush}, Emp
  in
  fix_traverse ~var ~ref

(* TODO: check that this isn't catastrophically wrong *)
let open_var k a ?twin:(twin = fun _ -> `Only) =
  let var k' i tw = if i = (k + k') then var ~twin:(twin tw) a else Ix (i, tw), Emp in
  let ref _n (b, tw, ush) = Ref {name = b; twin = tw; ushift = ush}, Emp in
  fix_traverse ~var ~ref

let unbind (B (nm, t)) =
  let x = Name.named nm in
  x, open_var 0 x t

let unbind_with x ?twin:(twin = fun _ -> `Only) (B (_, t)) =
  open_var 0 x ~twin t

let unbindn (NB (nms, t)) =
  let rec go k nms xs t =
    match nms with
    | [] -> xs, t
    | nm :: nms ->
      let x = Name.named nm in
      go (k + 1) nms (xs #< x) @@ open_var k x t
  in
  go 0 nms Emp t

let map_tm_face f (r, r', otm) =
  f r, f r', Option.map f otm

let map_tm_sys f =
  List.map @@ map_tm_face f

let unbind_ext (NB (nms, (ty, sys))) =
  let rec go k nms xs ty sys =
    match nms with
    | [] -> xs, ty, sys
    | nm :: nms ->
      let x = Name.named nm in
      go (k + 1) nms (xs #< x) (open_var k x ty) (map_tm_sys (open_var k x) sys)
  in
  go 0 nms Emp ty sys

let unbind_ext_with xs (NB (nms, (ty, sys))) =
  let rec go k xs ty sys =
    match xs with
    | [] -> ty, sys
    | x :: xs ->
      go (k + 1) xs (open_var k x ty) (map_tm_sys (open_var k x) sys)
  in
  if List.length nms = List.length xs then
    go 0 xs ty sys
  else
    failwith "unbind_ext_with: length mismatch"


let bind x tx =
  B (Name.name x, close_var x 0 tx)

let rec bindn xs txs =
  let xs_l = Bwd.to_list xs in
  let n = List.length xs_l - 1 in
  let rec go k xs txs =
    match xs with
    | Emp -> txs
    | Snoc (xs, x) ->
      go (k + 1) xs @@ close_var x (n - k) txs
  in
  NB (List.map Name.name xs_l, go 0 xs txs)

let rec bind_ext xs tyxs sysxs =
  let xs_l = Bwd.to_list xs in
  let n = List.length xs_l - 1 in
  let rec go k xs tyxs sysxs =
    match xs with
    | Emp -> tyxs, sysxs
    | Snoc (xs, x) ->
      go (k + 1) xs (close_var x (n - k) tyxs) (map_tm_sys (close_var x (n - k)) sysxs)
  in
  NB (List.map Name.name xs_l, go 0 xs tyxs sysxs)

let rec pp env fmt =

  let rec go env mode fmt (Tm t) =
    match t with
    | Pi (dom, B (nm, cod)) ->
      let x, env' = Pretty.Env.bind nm env in
      if mode = `Pi then
        Format.fprintf fmt "[%a : %a]@ %a" Uuseg_string.pp_utf_8 x (pp env) dom (go env' `Pi) cod
      else
        Format.fprintf fmt "@[<hv1>(%a @[<hv>[%a : %a]@ %a@])@]" Uuseg_string.pp_utf_8 "→" Uuseg_string.pp_utf_8 x (pp env) dom (go env' `Pi) cod

    | Sg (dom, B (nm, cod)) ->
      let x, env' = Pretty.Env.bind nm env in
      if mode = `Sg then
        Format.fprintf fmt "[%a : %a]@ %a" Uuseg_string.pp_utf_8 x (pp env) dom (go env' `Sg) cod
      else
        Format.fprintf fmt "@[<hv1>(%a @[<hv>[%a : %a]@ %a@])@]" Uuseg_string.pp_utf_8 "×" Uuseg_string.pp_utf_8 x (pp env) dom (go env' `Sg) cod

    | Ext (NB (nms, (cod, sys))) ->
      let xs, env' = Pretty.Env.bindn nms env in
      begin
        match sys with
        | [] ->
          Format.fprintf fmt "@[<hv1>(# <%a>@ %a)@]" pp_strings xs (pp env') cod
        | _ ->
          Format.fprintf fmt "@[<hv1>(# @[<hv1><%a>@ %a@ @[<hv>%a@]@])@]" pp_strings xs (pp env') cod (pp_sys env') sys
      end


    | Rst {ty; sys}  ->
      begin
        match sys with
        | [] ->
          Format.fprintf fmt "%a" (pp env) ty
        | _ ->
          Format.fprintf fmt "@[<hv1>(%a@ @[<hv>%a@])@]" (pp env) ty (pp_sys env) sys
      end

    | CoR face ->
      Format.fprintf fmt "@[<hv1>(=>@ %a)@]" (pp_face env) face

    | V info ->
      Format.fprintf fmt "@[<hv1>(V %a@ %a@ %a@ %a)@]" (pp env) info.r (pp env) info.ty0 (pp env) info.ty1 (pp env) info.equiv

    | VIn info ->
      Format.fprintf fmt "@[<hv1>(Vin %a@ %a@ %a)@]" (pp env) info.r (pp env) info.tm0 (pp env) info.tm1

    | Lam (B (nm, tm)) ->
      let x, env' = Pretty.Env.bind nm env in
      if mode = `Lam then
        Format.fprintf fmt "[%a]@ %a" Uuseg_string.pp_utf_8 x (go env' `Lam) tm
      else
        Format.fprintf fmt "@[<1>(λ [%a]@ %a)@]" Uuseg_string.pp_utf_8 x (go env' `Lam) tm

    | ExtLam (NB (nms, tm)) ->
      let xs, env' = Pretty.Env.bindn nms env in
      if mode = `Lam then
        Format.fprintf fmt "<%a>@ %a" pp_strings xs (go env' `Lam) tm
      else
        Format.fprintf fmt "@[<hv1>(λ <%a>@ %a)@]" pp_strings xs (go env' `Lam) tm

    | CoRThunk face ->
      pp_face env fmt face

    | Bool ->
      Format.fprintf fmt "bool"

    | Tt ->
      Format.fprintf fmt "tt"

    | Ff ->
      Format.fprintf fmt "ff"

    | Nat ->
      Format.fprintf fmt "nat"

    | Zero ->
      Format.fprintf fmt "zero"

    | Suc n ->
      Format.fprintf fmt "@[<hv1> (suc %a)@]" (go env `Suc) n

    | Int ->
      Format.fprintf fmt "int"

    | Pos n ->
      Format.fprintf fmt "@[<hv1> (pos %a)@]" (go env `Pos) n

    | NegSuc n ->
      Format.fprintf fmt "@[<hv1> (neg-suc %a)@]" (go env `NegSuc) n

    | Dim0 ->
      Format.fprintf fmt "0"

    | Dim1 ->
      Format.fprintf fmt "1"

    | S1 ->
      Format.fprintf fmt "S1"

    | Base ->
      Format.fprintf fmt "base"

    | Loop r ->
      Format.fprintf fmt "(loop %a)" (pp env) r

    | Univ {kind; lvl} ->
      Format.fprintf fmt "(U %a %a)" Kind.pp kind Lvl.pp lvl

    | FCom {r; r'; cap; sys} ->
      Format.fprintf fmt "@[<hv1>(fcom %a %a@ %a@ @[%a@])@]" (pp env) r (pp env) r' (pp env) cap (pp_bsys env) sys

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
      Format.fprintf fmt "@[<hv1>(cons@ %a@ %a)@]" (pp env) tm0 (pp env) tm1

    | Box {r; r'; cap; sys} ->
      Format.fprintf fmt "@[<hv1>(box %a %a@ %a@ @[<hv>%a@])@]" (pp env) r (pp env) r' (pp env) cap (pp_sys env) sys

    | Let (cmd, B (nm, t)) ->
      let x, env' = Pretty.Env.bind nm env in
      Format.fprintf fmt "@[<hv1>(let@ @[<hv1>[%a %a]@]@ %a)@]" Uuseg_string.pp_utf_8 x (pp_cmd env) cmd (pp env') t

    | Up cmd ->
      pp_cmd env fmt cmd

  in
  go env `Start fmt

and pp_head env fmt =
  function
  | Coe {r; r'; ty = B (nm, ty); tm} ->
    let x, env' = Pretty.Env.bind nm env in
    Format.fprintf fmt "@[<hv1>(coe %a %a@ <%a> %a@ %a)@]" (pp env) r (pp env) r' Uuseg_string.pp_utf_8 x (pp env') ty (pp env) tm

  | HCom {r; r'; ty; cap; sys} ->
    Format.fprintf fmt "@[<hv1>(hcom %a %a@ %a@ %a@ @[%a@])@]" (pp env) r (pp env) r' (pp env) ty (pp env) cap (pp_bsys env) sys

  | Com {r; r'; ty = B (nm, ty); cap; sys} ->
    let x, env' = Pretty.Env.bind nm env in
    Format.fprintf fmt "@[<hv1>(com %a %a@ [%a] %a@ %a@ @[%a@])@]" (pp env) r (pp env) r' Uuseg_string.pp_utf_8 x (pp env') ty (pp env) cap (pp_bsys env) sys

  | GHCom {r; r'; ty; cap; sys} ->
    Format.fprintf fmt "@[<hv1>(ghcom %a %a@ %a@ %a@ @[%a@])@]" (pp env) r (pp env) r' (pp env) ty (pp env) cap (pp_bsys env) sys

  | GCom {r; r'; ty = B (nm, ty); cap; sys} ->
    let x, env' = Pretty.Env.bind nm env in
    Format.fprintf fmt "@[<hv1>(gcom %a %a@ [%a] %a@ %a@ @[%a@])@]" (pp env) r (pp env) r' Uuseg_string.pp_utf_8 x (pp env') ty (pp env) cap (pp_bsys env) sys

  | Ix (ix, _tw) ->
    Uuseg_string.pp_utf_8 fmt @@
    Pretty.Env.var ix env

  | Ref {name; ushift} ->
    Name.pp fmt name;
    if ushift > 0 then Format.fprintf fmt "^%i" ushift else ()

  | Meta {name; ushift} ->
    Format.fprintf fmt "?%a^%i"
      Name.pp name
      ushift

  | Down {ty; tm} ->
    Format.fprintf fmt "@[<hv1>(%a@ %a@ %a)@]" Uuseg_string.pp_utf_8 "▷" (pp env) ty (pp env) tm

and pp_cmd env fmt (hd, sp) =
  let rec go mode fmt sp =
    match sp with
    | Emp -> pp_head env fmt hd
    | Snoc (sp, f)->
      match f with
      | Car ->
        Format.fprintf fmt "@[<hv1>(car@ %a)@]" (go `Car) sp
      | Cdr ->
        Format.fprintf fmt "@[<hv1>(cdr@ %a)@]" (go `Car) sp
      | FunApp t ->
        if mode = `FunApp then
          Format.fprintf fmt "%a@ %a" (go `FunApp) sp (pp env) t
        else
          Format.fprintf fmt "@[<hv1>(%a@ %a)@]" (go `FunApp) sp (pp env) t
      | ExtApp ts ->
        Format.fprintf fmt "@[<hv1>(%s %a@ %a)@]" "@" (go `ExtApp) sp (pp_terms env) ts
      | If {mot = B (nm, mot); tcase; fcase} ->
        let x, env' = Pretty.Env.bind nm env in
        Format.fprintf fmt "@[<hv1>(if@ [%a] %a@ %a@ %a@ %a)@]" Uuseg_string.pp_utf_8 x (pp env') mot (go `If) sp (pp env) tcase (pp env) fcase
      | S1Rec {mot = B (nm_mot, mot); bcase; lcase = B (nm_lcase, lcase)} ->
        let x_mot, env_mot = Pretty.Env.bind nm_mot env in
        let x_lcase, env_lcase = Pretty.Env.bind nm_lcase env in
        Format.fprintf fmt "@[<hv1>(S1rec@ [%a] %a@ %a %a [%a] %a)@]" Uuseg_string.pp_utf_8 x_mot (pp env_mot) mot (go `S1Rec) sp (pp env) bcase Uuseg_string.pp_utf_8 x_lcase (pp env_lcase) lcase
      | VProj {r; ty0; ty1; equiv} ->
        Format.fprintf fmt "@[<hv1>(vproj %a@ %a@ %a@ %a@ %a)@]" (pp env) r (go `VProj) sp (pp env) ty0 (pp env) ty1 (pp env) equiv
      | Cap _ ->
        (* FIXME *)
        Format.fprintf fmt "@<cap>"
      | LblCall ->
        Format.fprintf fmt "@[<hv1>(call@ %a)@]" (go `Call) sp
      | CoRForce ->
        Format.fprintf fmt "@[<hv1>(force@ %a)@]" (go `Force) sp
  in
  go `Start fmt sp

and pp_spine env fmt sp =
  match sp with
  | Emp ->
    Format.fprintf fmt "[]"
  | Snoc (sp, f) ->
    Format.fprintf fmt "%a; %a"
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
  | If _ ->
    Format.fprintf fmt "<if>"
  | _ ->
    Format.fprintf fmt "<frame>"

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
    let x, env' = Pretty.Env.bind nm env in
    Format.fprintf fmt "@[<hv1>[%a=%a@ <%a> %a]@]" (pp env) r (pp env) r' Uuseg_string.pp_utf_8 x (pp env') tm


let up cmd = make @@ Up cmd

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

module Macro =
struct
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
    make @@ Ext (NB ([None], (ty', sys)))

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
end

module OccursAux =
struct
  let rec go fl tm acc =
    match unleash tm with
    | Lam bnd ->
      go_bnd fl bnd acc
    | Pi (dom, cod) ->
      go_bnd fl cod @@
      go fl dom acc
    | Sg (dom, cod) ->
      go_bnd fl cod @@
      go fl dom acc
    | Ext ebnd ->
      go_ext_bnd fl ebnd acc
    | Rst info ->
      go fl info.ty @@
      go_tm_sys fl info.sys acc
    | Up cmd ->
      go_cmd fl cmd acc
    | ExtLam nbnd ->
      go_nbnd fl nbnd acc
    | (Bool | Tt | Ff | Dim0 | Dim1 | Univ _) ->
      acc
    | Cons (t0, t1) ->
      go fl t1 @@ go fl t0 acc
    | Let (cmd, bnd) ->
      go_bnd fl bnd @@ go_cmd fl cmd acc
    | V info ->
      go fl info.r @@ go fl info.ty0 @@
      go fl info.ty1 @@ go fl info.equiv acc
    | VIn info ->
      go fl info.r @@ go fl info.tm0 @@
      go fl info.tm1 acc
    | FCom info ->
      go fl info.r @@ go fl info.r' @@ go fl info.cap @@
      go_comp_sys fl info.sys @@ acc
    | CoRThunk face ->
      go_tm_face fl face acc
    | _ ->
      Format.eprintf "Tried to get free variables, but we didn't implement the case for: %a@." (pp Pretty.Env.emp) tm;
      failwith "TODO"

  and go_cmd fl (hd, sp) acc =
    match fl, hd with
    | `RigVars, Ref {name; _} ->
      go_spine fl sp @@
      Occurs.Set.add name acc
    | `RigVars, Meta _ ->
      acc
    | _ ->
      go_spine fl sp @@
      go_head fl hd acc

  and go_head fl hd acc =
    match fl, hd with
    | _, Ix _ -> acc
    | `Vars, Meta _ -> acc
    | `RigVars, Meta _ -> acc
    | `Metas, Meta {name; _} ->
      Occurs.Set.add name acc
    | (`Vars | `RigVars), Ref {name; _} ->
      Occurs.Set.add name acc
    | `Metas, Ref _ -> acc
    | _, Down {ty; tm} ->
      go fl tm @@ go fl ty acc
    | _, Coe info ->
      go fl info.r @@
      go fl info.r' @@
      go_bnd fl info.ty @@
      go fl info.tm acc
    | _, HCom info ->
      go fl info.r @@
      go fl info.r' @@
      go fl info.ty @@
      go fl info.cap @@
      go_comp_sys fl info.sys acc
    | _, Com info ->
      go fl info.r @@
      go fl info.r' @@
      go_bnd fl info.ty @@
      go fl info.cap @@
      go_comp_sys fl info.sys acc
    | _, GHCom info ->
      go fl info.r @@
      go fl info.r' @@
      go fl info.ty @@
      go fl info.cap @@
      go_comp_sys fl info.sys acc
    | _, GCom info ->
      go fl info.r @@
      go fl info.r' @@
      go_bnd fl info.ty @@
      go fl info.cap @@
      go_comp_sys fl info.sys acc

  and go_spine fl sp =
    List.fold_right (go_frame fl) @@ Bwd.to_list sp

  and go_frame fl frm acc =
    match frm with
    | (Car | Cdr | LblCall | CoRForce) -> acc
    | FunApp t ->
      go fl t acc
    | ExtApp ts ->
      List.fold_right (go fl) ts acc
    | If info ->
      go_bnd fl info.mot @@
      go fl info.tcase @@
      go fl info.fcase acc
    | S1Rec info ->
      go_bnd fl info.mot @@
      go fl info.bcase @@
      go_bnd fl info.lcase acc
    | VProj info ->
      go fl info.r @@
      go fl info.ty0 @@
      go fl info.ty1 @@
      go fl info.equiv acc
    | Cap info ->
      go fl info.r @@
      go fl info.r' @@
      go_comp_sys fl info.sys acc

  and go_ext_bnd fl bnd acc =
    let NB (_, (ty, sys)) = bnd in
    go fl ty @@ go_tm_sys fl sys acc


  and go_nbnd fl bnd acc =
    let NB (_, tm) = bnd in
    go fl tm acc

  and go_bnd fl bnd acc =
    let B (_, tm) = bnd in
    go fl tm acc

  and go_tm_sys fl =
    List.fold_right @@ go_tm_face fl

  and go_comp_sys fl =
    List.fold_right @@ go_comp_face fl

  and go_tm_face fl (r, r', otm) acc =
    go fl r @@ go fl r' @@
    match otm with
    | None -> acc
    | Some tm -> go fl tm acc

  and go_comp_face fl (r, r', obnd) acc =
    go fl r @@ go fl r' @@
    match obnd with
    | None -> acc
    | Some bnd -> go_bnd fl bnd acc
end

let free fl tm =
  (* Format.eprintf "Free: %a@." (pp Pretty.Env.emp) tm; *)
  OccursAux.go fl tm Occurs.Set.empty

module Sp =
struct
  type t = tm spine
  let free fl sp =
    OccursAux.go_spine fl sp Occurs.Set.empty
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
  | Ref info -> Ref info
  | Meta a -> Meta a
  | Ix (i, tw) -> Ix (i, tw)
  | Down info ->
    let ty = f info.ty in
    let tm = f info.tm in
    Down {ty; tm}
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
  | (Car | Cdr | LblCall | CoRForce) as frm ->
    frm
  | FunApp t ->
    FunApp (f t)
  | ExtApp ts ->
    ExtApp (List.map f ts)
  | If info ->
    let mot = map_bnd f info.mot in
    let tcase = f info.tcase in
    let fcase = f info.fcase in
    If {mot; tcase; fcase}
  | S1Rec info ->
    let mot = map_bnd f info.mot in
    let bcase = f info.bcase in
    let lcase = map_bnd f info.lcase in
    S1Rec {mot; bcase; lcase}
  | VProj info ->
    let r = f info.r in
    let ty0 = f info.ty0 in
    let ty1 = f info.ty1 in
    let equiv = f info.equiv in
    VProj {r; ty0; ty1; equiv}
  | Cap info ->
    let r = f info.r in
    let r' = f info.r' in
    let ty = f info.ty in
    let sys = map_comp_sys f info.sys in
    Cap {r; r'; ty; sys}

let map_spine f =
  Bwd.map @@ map_frame f


(* TODO: clean up: this is catastrophically bad *)
let rec map_ext_bnd f nbnd =
  match nbnd with
  | NB ([], (ty, sys)) ->
    NB ([], (f ty, map_tm_sys f sys))
  | NB (nm :: nms, (ty, sys)) ->
    let x = Name.named nm in
    let tyx = open_var 0 x ty in
    let sysx = map_tm_sys (open_var 0 x) sys in
    let NB (_, (tyx', sysx')) = map_ext_bnd f (NB (nms, (tyx, sysx))) in
    NB (nm :: nms, (close_var x 0 tyx', map_tm_sys (close_var x 0) sysx'))

let map_cmd f (hd, sp) =
  map_head f hd, map_spine f sp

let map_tmf f =
  function
  | (Univ _ | Bool | Tt | Ff | Nat | Zero | Int | Dim0 | Dim1 | S1 | Base) as con ->
    con
  | Suc n -> Suc (f n)
  | Pos n -> Pos (f n)
  | NegSuc n -> NegSuc (f n)
  | Loop r -> Loop (f r)
  | Cons (t0, t1) ->
    Cons (f t0, f t1)
  | LblRet t ->
    LblRet (f t)
  | FCom info ->
    let r = f info.r in
    let r' = f info.r' in
    let cap = f info.cap in
    let sys = map_comp_sys f info.sys in
    FCom {r; r'; cap; sys}
  | Pi (dom, cod) ->
    Pi (f dom, map_bnd f cod)
  | Sg (dom, cod) ->
    Sg (f dom, map_bnd f cod)
  | Ext ebnd ->
    Ext (map_ext_bnd f ebnd)
  | Rst {ty; sys} ->
    Rst {ty = f ty; sys = map_tm_sys f sys}
  | CoR face ->
    CoR (map_tm_face f face)
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
  | CoRThunk face ->
    CoRThunk (map_tm_face f face)
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
  | Up cmd ->
    Up (map_cmd f cmd)
  | Let (cmd, bnd) ->
    Let (map_cmd f cmd, map_bnd f bnd)



let rec opt_traverse f xs =
  match xs with
  | [] -> Some []
  | x::xs ->
    match f x with
    | Some y -> Option.map (fun ys -> y :: ys) @@ opt_traverse f xs
    | None -> None


let as_plain_var t =
  match unleash t with
  | Up (Ref {name; _}, Emp) ->
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
  match unleash tm with
  | Univ {lvl; kind} ->
    make @@ Univ {lvl = Lvl.shift k lvl; kind}
  | Up (Ref info, sp) ->
    let hd' = Ref {info with ushift = info.ushift + k} in
    let sp' = map_spine (shift_univ k) sp in
    make @@ Up (hd', sp')
  | Up (Meta {name; ushift}, sp) ->
    let hd' = Meta {name; ushift = ushift + k} in
    let sp' = map_spine (shift_univ k) sp in
    make @@ Up (hd', sp')
  | tmf ->
    Tm (map_tmf (shift_univ k) tmf)

let pp0 fmt tm = pp Pretty.Env.emp fmt @@ eta_contract tm
