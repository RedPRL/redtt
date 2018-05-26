open RedBasis

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
  | Sg of 'a * 'a bnd

  | V of {r : 'a; ty0 : 'a; ty1 : 'a; equiv : 'a}

  | Bool
  | Tt
  | Ff

  | Lam of 'a bnd
  | ExtLam of 'a nbnd

  | Cons of 'a * 'a
  | Dim0
  | Dim1

  (* Labelled types from Epigram *)
  | LblTy of {lbl : string; args : ('a * 'a) list; ty : 'a}
  | LblRet of 'a

  | Up of 'a cmd
  | Let of 'a cmd * 'a bnd

and 'a head =
  | Meta of Name.t
  | Ref of Name.t
  | Ix of int
  | Down of {ty : 'a; tm : 'a}
  | Coe of {r : 'a; r' : 'a; ty : 'a bnd; tm : 'a}
  | HCom of {r : 'a; r' : 'a; ty : 'a; cap : 'a; sys : ('a, 'a bnd) system}
  | Com of {r : 'a; r' : 'a; ty : 'a bnd; cap : 'a; sys : ('a, 'a bnd) system}


and 'a frame =
  | Car
  | Cdr
  | FunApp of 'a
  | ExtApp of 'a list
  | If of {mot : 'a bnd; tcase : 'a; fcase : 'a}
  | VProj of {r : 'a; ty0 : 'a; ty1 : 'a; equiv : 'a}
  | LblCall

and 'a stack = 'a frame list
and 'a cmd = Cut of 'a head * 'a stack

type tm = Tm of tm tmf

type subst =
  | Id
  | Proj
  | Sub of subst * tm cmd
  | Cmp of subst * subst

let ($$) hd stk =
  Cut (hd, stk)

let var i =
  Ix i $$ []

let lift sub =
  Sub (Cmp (sub, Proj), var 0)

let rec liftn n sub =
  match n with
  | 0 -> sub
  | _ -> liftn (n - 1) @@ lift sub

let inst0 t = Sub (Id, t)


let rec subst (sub : subst) (Tm con) =
  Tm (subst_f sub con)

and subst_f (sub : subst) =
  function
  | (Dim0 | Dim1 | Univ _ | Bool | Tt | Ff) as con ->
    con

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

  | V info ->
    let r = subst sub info.r in
    let ty0 = subst sub info.ty0 in
    let ty1 = subst sub info.ty1 in
    let equiv = subst sub info.equiv in
    V {r; ty0; ty1; equiv}

  | Lam bnd ->
    Lam (subst_bnd sub bnd)

  | ExtLam nbnd ->
    ExtLam (subst_nbnd sub nbnd)

  | Cons (t0, t1) ->
    Cons (subst sub t0, subst sub t1)

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


and subst_cmd sub =
  function Cut (head, spine) ->
    let Cut (head', spine') = subst_head sub head in
    let spine'' = subst_spine sub spine in
    Cut (head', spine' @ spine'')

and subst_spine sub spine =
  List.map (subst_frame sub) spine

and subst_frame sub frame =
  match frame with
  | (Car | Cdr | LblCall) ->
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
  | VProj info ->
    let r = subst sub info.r in
    let ty0 = subst sub info.ty0 in
    let ty1 = subst sub info.ty1 in
    let equiv = subst sub info.equiv in
    VProj {r; ty0; ty1; equiv}

and subst_head sub head =
  match head with
  | Ix i ->
    subst_ix sub i

  | Ref a ->
    Ref a $$ []

  | Meta a ->
    Meta a $$ []

  | Down info ->
    let ty = subst sub info.ty in
    let tm = subst sub info.tm in
    Down {ty; tm} $$ []

  | HCom info ->
    let r = subst sub info.r in
    let r' = subst sub info.r' in
    let ty = subst sub info.ty in
    let cap = subst sub info.cap in
    let sys = subst_comp_sys sub info.sys in
    HCom {r; r'; ty; cap; sys} $$ []

  | Coe info ->
    let r = subst sub info.r in
    let r' = subst sub info.r' in
    let ty = subst_bnd sub info.ty in
    let tm = subst sub info.tm in
    Coe {r; r'; ty; tm} $$ []

  | Com info ->
    let r = subst sub info.r in
    let r' = subst sub info.r' in
    let ty = subst_bnd sub info.ty in
    let cap = subst sub info.cap in
    let sys = subst_comp_sys sub info.sys in
    Com {r; r'; ty; cap; sys} $$ []

and subst_ix sub ix  =
  match sub with
  | Id ->
    Ix ix $$ []
  | Proj ->
    Ix (ix + 1) $$ []

  | Sub (sub, cmd) ->
    if ix = 0 then cmd else subst_ix sub (ix - 1)

  | Cmp (sub1, sub0) ->
    subst_cmd sub1 @@
    subst_ix sub0 ix

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

let make con = Tm con
let unleash (Tm con) = con

let traverse ~f ~var ~ref =
  let rec go k =
    function
    | Univ info -> Univ info
    | Bool -> Bool
    | Tt -> Tt
    | Ff -> Ff
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
    | ExtLam nbnd ->
      ExtLam (go_nbnd k nbnd)
    | Cons (t0, t1) ->
      Cons (f k t0, f k t1)
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

  and go_cmd k =
    function Cut (hd, stk) ->
      let Cut (hd', stk') = go_hd k hd in
      let stk'' = go_stk k stk in
      Cut (hd', stk' @ stk'')

  and go_hd k =
    function
    | Ix i ->
      var i
    | Ref a ->
      ref k a
    | Meta a ->
      Meta a $$ []
    | Down info ->
      let ty = f k info.ty in
      let tm = f k info.tm in
      Down {ty; tm} $$ []
    | Coe info ->
      let r = f k info.r in
      let r' = f k info.r' in
      let ty = go_bnd k info.ty in
      let tm = f k info.tm in
      Coe {r; r'; ty; tm} $$ []
    | HCom info ->
      let r = f k info.r in
      let r' = f k info.r' in
      let ty = f k info.ty in
      let cap = f k info.cap in
      let sys = go_comp_sys k info.sys in
      HCom {r; r'; ty; cap; sys} $$ []
    | Com info ->
      let r = f k info.r in
      let r' = f k info.r' in
      let ty = go_bnd k info.ty in
      let cap = f k info.cap in
      let sys = go_comp_sys k info.sys in
      Com {r; r'; ty; cap; sys} $$ []

  and go_stk k =
    List.map (go_frm k)

  and go_frm k =
    function
    | (Car | Cdr | LblCall) as frm -> frm
    | FunApp t ->
      FunApp (f k t)
    | ExtApp ts ->
      ExtApp (List.map (f k) ts)
    | If info ->
      let mot = go_bnd k info.mot in
      let tcase = f k info.tcase in
      let fcase = f k info.fcase in
      If {mot; tcase; fcase}
    | VProj info ->
      let r = f k info.r in
      let ty0 = f k info.ty0 in
      let ty1 = f k info.ty1 in
      let equiv = f k info.equiv in
      VProj {r; ty0; ty1; equiv}


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

let close_var a k =
  let var i = Ix i $$ [] in
  let ref n b = if b = a then Ix (n + k) $$ [] else Ref b $$ [] in
  fix_traverse ~var ~ref

let subst sub =
  let ref _ b = Ref b $$ [] in
  let rec go k (Tm tm) =
    let var i = subst_ix (liftn k sub) i in
    Tm (traverse ~f:go ~var ~ref k tm)
  in
  go 0

let open_var k a t =
  subst (liftn k @@ inst0 @@ Cut (Ref a, [])) t

let unbind (B (nm, t)) =
  let x = Name.named nm in
  x, open_var 0 x t

let bind x tx =
  B (Some (Name.to_string x), close_var x 0 tx)

let rec pp env fmt (Tm tm) =
  match tm with

  | Pi (dom, B (nm, cod)) ->
    let x, env' = Pretty.Env.bind nm env in
    Format.fprintf fmt "@[<1>(%a [%a : %a]@ %a)@]" Uuseg_string.pp_utf_8 "→" Uuseg_string.pp_utf_8 x (pp env) dom (pp env') cod

  | Sg (dom, B (nm, cod)) ->
    let x, env' = Pretty.Env.bind nm env in
    Format.fprintf fmt "@[<1>(%a [%a : %a]@ %a)@]" Uuseg_string.pp_utf_8 "×" Uuseg_string.pp_utf_8 x (pp env) dom (pp env') cod

  | Ext (NB (nms, (cod, sys))) ->
    let xs, env' = Pretty.Env.bindn nms env in
    begin
      match sys with
      | [] ->
        Format.fprintf fmt "@[<1>(# <%a>@ %a)@]" pp_strings xs (pp env') cod
      | _ ->
        Format.fprintf fmt "@[<1>(# @[<1><%a>@ %a@ @[%a@]@])@]" pp_strings xs (pp env') cod (pp_sys env') sys
    end


  | Rst {ty; sys}  ->
    begin
      match sys with
      | [] ->
        Format.fprintf fmt "%a" (pp env) ty
      | _ ->
        Format.fprintf fmt "@[<1>(%a@ @[%a@])@]" (pp env) ty (pp_sys env) sys
    end

  | V info ->
    Format.fprintf fmt "@[<1>(V %a@ %a@ %a@ %a)!]" (pp env) info.r (pp env) info.ty0 (pp env) info.ty1 (pp env) info.equiv

  | Lam (B (nm, tm)) ->
    let x, env' = Pretty.Env.bind nm env in
    Format.fprintf fmt "@[<1>(λ [%a]@ %a)@]" Uuseg_string.pp_utf_8 x (pp env') tm

  | ExtLam (NB (nms, tm)) ->
    let xs, env' = Pretty.Env.bindn nms env in
    Format.fprintf fmt "@[<1>(λ <%a>@ %a)@]" pp_strings xs (pp env') tm

  | Bool ->
    Format.fprintf fmt "bool"

  | Tt ->
    Format.fprintf fmt "tt"

  | Ff ->
    Format.fprintf fmt "ff"

  | Dim0 ->
    Format.fprintf fmt "0"

  | Dim1 ->
    Format.fprintf fmt "1"

  | Univ {kind; lvl} ->
    Format.fprintf fmt "(U %a %a)" Kind.pp kind Lvl.pp lvl

  | FCom {r; r'; cap; sys} ->
    Format.fprintf fmt "@[<1>(fcom %a %a@ %a@ @[%a@])@]" (pp env) r (pp env) r' (pp env) cap (pp_bsys env) sys

  | LblTy {lbl; args; ty} ->
    begin
      match args with
      | [] ->
        Format.fprintf fmt "@[<1>{%a : %a}@]"
          Uuseg_string.pp_utf_8 lbl
          (pp env) ty
      | _ ->
        Format.fprintf fmt "@[<1>{%a %a : %a}@]"
          Uuseg_string.pp_utf_8 lbl
          (pp_terms env) (List.map snd args)
          (pp env) ty
    end

  | LblRet t ->
    Format.fprintf fmt "@[<1>(ret@ %a)@]"
      (pp env) t

  | Cons (tm0, tm1) ->
    Format.fprintf fmt "@[<1>(cons@ %a@ %a)@]" (pp env) tm0 (pp env) tm1

  | Let (cmd, B (nm, t)) ->
    let x, env' = Pretty.Env.bind nm env in
    Format.fprintf fmt "@[<1>(let@ @[<1>[%a %a]@]@ %a)@]" Uuseg_string.pp_utf_8 x (pp_cmd env) cmd (pp env') t

  | Up cmd ->
    pp_cmd env fmt cmd

and pp_head env fmt =
  function
  | Coe {r; r'; ty = B (nm, ty); tm} ->
    let x, env' = Pretty.Env.bind nm env in
    Format.fprintf fmt "@[<1>(coe %a %a@ [%a] %a@ %a)@]" (pp env) r (pp env) r' Uuseg_string.pp_utf_8 x (pp env') ty (pp env) tm

  | HCom {r; r'; ty; cap; sys} ->
    Format.fprintf fmt "@[<1>(hcom %a %a@ %a@ %a@ @[%a@])@]" (pp env) r (pp env) r' (pp env) ty (pp env) cap (pp_bsys env) sys


  | Com {r; r'; ty = B (nm, ty); cap; sys} ->
    let x, _env' = Pretty.Env.bind nm env in
    Format.fprintf fmt "@[<1>(com %a %a@ [%a] %a@ %a@ @[%a@])@]" (pp env) r (pp env) r' Uuseg_string.pp_utf_8 x (pp env) ty (pp env) cap (pp_bsys env) sys

  | Ix i ->
    Uuseg_string.pp_utf_8 fmt @@
    Pretty.Env.var i env

  | Ref nm ->
    Name.pp fmt nm

  | Meta nm ->
    Format.fprintf fmt "?%a"
      Name.pp nm

  | Down {ty; tm} ->
    Format.fprintf fmt "@[<1>(%a@ %a@ %a)@]" Uuseg_string.pp_utf_8 "▷" (pp env) ty (pp env) tm

and pp_cmd env fmt =
  function Cut (hd, sp) ->
    let rec go fmt sp =
      match sp with
      | [] -> pp_head env fmt hd
      | f :: sp ->
        match f with
        | Car ->
          Format.fprintf fmt "@[<1>(car@ %a)@]" go sp
        | Cdr ->
          Format.fprintf fmt "@[<1>(cdr@ %a)@]" go sp
        | FunApp t ->
          Format.fprintf fmt "@[<1>(%a@ %a)@]" go sp (pp env) t
        | ExtApp ts ->
          Format.fprintf fmt "@[<1>(%s %a@ %a)@]" "@" go sp (pp_terms env) ts
        | If {mot = B (nm, mot); tcase; fcase} ->
          let x, env' = Pretty.Env.bind nm env in
          Format.fprintf fmt "@[<1>(if@ [%a] %a@ %a %a %a)@]" Uuseg_string.pp_utf_8 x (pp env') mot go sp (pp env) tcase (pp env) fcase
        | VProj {r; _} ->
          (* TODO *)
          Format.fprintf fmt "@[<1>(vproj %a@ %a)@]" (pp env) r go sp
        | LblCall ->
          Format.fprintf fmt "@[<1>(call@ %a)@]" go sp
    in
    go fmt (List.rev sp)

and pp_terms env fmt ts =
  let pp_sep fmt () = Format.fprintf fmt " " in
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
    Format.fprintf fmt "@[<1>[%a=%a@ -]@]" (pp env) r (pp env) r'

  | Some tm ->
    Format.fprintf fmt "@[<1>[%a=%a@ %a]@]" (pp env) r (pp env) r' (pp env) tm

and pp_bface env fmt face =
  let r, r', obnd = face in
  match obnd with
  | None ->
    Format.fprintf fmt "@[<1>[%a=%a@ -]@]" (pp env) r (pp env) r'

  | Some (B (nm, tm)) ->
    let x, env' = Pretty.Env.bind nm env in
    Format.fprintf fmt "@[<1>[%a=%a@ <%a> %a]@]" (pp env) r (pp env) r' Uuseg_string.pp_utf_8 x (pp env') tm

let up cmd = make @@ Up cmd

let car =
  function Cut (hd, sp) ->
    Cut (hd, sp @ [Car])

let cdr =
  function Cut (hd, sp) ->
    Cut (hd, sp @ [Cdr])

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
    subst Proj ty1

  let times ty0 ty1 =
    sg None ty0 @@
    subst Proj ty1

  let path ty tm0 tm1 =
    let ty' = subst Proj ty in
    let face0 = up (var 0), make Dim0, Some (subst Proj tm0) in
    let face1 = up (var 0), make Dim1, Some (subst Proj tm1) in
    let sys = [face0; face1] in
    make @@ Ext (NB ([None], (ty', sys)))

  let fiber ~ty0 ~ty1 ~f ~x =
    sg None ty0 @@
    path
      (subst Proj ty1)
      (up @@ (Ix 0 $$ [FunApp (subst Proj f)]))
      (subst Proj x)

  let proj2 = Cmp (Proj, Proj)

  let is_contr ty =
    sg None ty @@
    pi None (subst Proj ty) @@
    path
      (subst proj2 ty)
      (up @@ var 0)
      (up @@ var 1)

  let equiv ty0 ty1 =
    sg None (arr ty0 ty1) @@
    pi None (subst Proj ty1) @@
    is_contr @@
    fiber
      ~ty0:(subst proj2 ty0)
      ~ty1:(subst proj2 ty1)
      ~f:(up @@ var 1)
      ~x:(up @@ var 0)
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
    | Up cmd ->
      go_cmd fl cmd acc
    | _ -> failwith ""

  and go_cmd fl cmd acc =
    match cmd with
    | Cut (hd, stk) ->
      match fl, hd with
      | `RigVars, Ref x ->
        go_stack fl stk @@
        Occurs.Set.add x acc
      | `RigVars, Meta _ ->
        acc
      | _ ->
        go_stack fl stk @@
        go_head fl hd acc

  and go_head fl hd acc =
    match fl, hd with
    | _, Ix _ -> acc
    | `Vars, Meta _ -> acc
    | `RigVars, Meta _ -> acc
    | `Metas, Meta alpha ->
      Occurs.Set.add alpha acc
    | (`Vars | `RigVars), Ref x ->
      Occurs.Set.add x acc
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

  and go_stack fl stk =
    List.fold_right (go_frame fl) stk

  and go_frame fl frm acc =
    match frm with
    | Car -> acc
    | Cdr -> acc
    | LblCall -> acc
    | FunApp t ->
      go fl t acc
    | ExtApp ts ->
      List.fold_right (go fl) ts acc
    | If info ->
      go_bnd fl info.mot @@
      go fl info.tcase @@
      go fl info.fcase acc
    | VProj info ->
      go fl info.r @@
      go fl info.ty0 @@
      go fl info.ty1 @@
      go fl info.equiv acc

  and go_ext_bnd fl bnd acc =
    let NB (_, (ty, sys)) = bnd in
    go fl ty @@ go_tm_sys fl sys acc

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
  OccursAux.go fl tm Occurs.Set.empty

module Stk =
struct
  type t = tm stack
  let free fl stk =
    OccursAux.go_stack fl stk Occurs.Set.empty
end
