open RedBasis

type 'a bnd = B of string option * 'a
type 'a nbnd = NB of string option list * 'a

type chk = [`Chk]
type inf = [`Inf]

type info = Lexing.position * Lexing.position

type _ f =
  | Global : string -> inf f
  | Var : int -> inf f
  | Car : inf t -> inf f
  | Cdr : inf t -> inf f
  | FunApp : inf t * chk t -> inf f
  | ExtApp : inf t * chk t list -> inf f

  | Down : {ty : chk t; tm : chk t} -> inf f
  | Coe : {r : chk t; r' : chk t; ty : chk t bnd; tm : chk t} -> inf f
  | HCom : {r : chk t; r' : chk t; ty : chk t; cap : chk t; sys : chk t bnd system} -> inf f
  | Com : {r : chk t; r' : chk t; ty : chk t bnd; cap : chk t; sys : chk t bnd system} -> inf f

  | FCom : {r : chk t; r' : chk t; cap : chk t; sys : chk t bnd system} -> chk f

  | Up : inf t -> chk f

  | Univ : {kind : Kind.t; lvl : Lvl.t} -> chk f
  | Pi : chk t * chk t bnd -> chk f
  | Ext : (chk t * chk t system) nbnd -> chk f
  | Rst : {ty : chk t; sys : chk t system} -> chk f
  | Sg : chk t * chk t bnd -> chk f

  | V : {r : chk t; ty0 : chk t; ty1 : chk t; equiv : chk t} -> chk f

  | Bool : chk f
  | Tt : chk f
  | Ff : chk f
  | If : {mot : chk t bnd; scrut : inf t; tcase : chk t; fcase : chk t} -> inf f
  | VProj : {r : chk t; tm : chk t; ty0 : chk t; ty1 : chk t; equiv : chk t} -> inf f

  | Lam : chk t bnd -> chk f
  | ExtLam : chk t nbnd -> chk f

  | Cons : chk t * chk t -> chk f
  | Dim0 : chk f
  | Dim1 : chk f

  | Let : inf t * chk t bnd -> chk f

and subst =
  | Id
  | Proj
  | Sub of subst * inf t
  | Cmp of subst * subst

and 'a node = {info : info option; con : 'a f; subst : subst}
and 'a t = 'a node ref
and 'a face = chk t * chk t * 'a option
and 'a system = 'a face list


let make tf = ref {info = None; con = tf; subst = Id}
let into_info info tf = ref {info = info; con = tf; subst = Id}
let info node = !node.info

let var i = make @@ Var i
let lift sub = Sub (sub, var 0)
let rec liftn n sub =
  match n with
  | 0 -> sub
  | _ -> liftn (n - 1) @@ lift sub

let inst0 t = Sub (Id, t)

let subst : type x. subst -> x t -> x t =
  fun sub node ->
    ref {!node with subst = Cmp (sub, !node.subst)}

let subst_bnd : subst -> 'a t bnd -> 'a t bnd =
  fun sub bnd ->
    let B (nm, t) = bnd in
    B (nm, subst (lift sub) t)

let subst_nbnd : subst -> 'a t nbnd -> 'a t nbnd =
  fun sub bnd ->
    let NB (nms, t) = bnd in
    NB (nms, subst (liftn (List.length nms) sub) t)

let rec substf : type x. subst -> x f -> x f =
  fun sub con ->
    match sub with
    | Id -> con
    | _ ->
      match con with
      | Var ix ->
        proj sub ix

      | Global _ -> con
      | Bool -> con
      | Tt -> con
      | Ff -> con
      | Dim0 -> con
      | Dim1 -> con
      | Univ _ -> con

      | Car t ->
        Car (subst sub t)

      | Cdr t ->
        Cdr (subst sub t)

      | FunApp (t0, t1) ->
        FunApp (subst sub t0, subst sub t1)

      | ExtApp (t0, ts) ->
        ExtApp (subst sub t0, List.map (subst sub) ts)

      | Down {ty; tm} ->
        Down {ty = subst sub ty; tm = subst sub tm}

      | Coe info ->
        let r = subst sub info.r in
        let r' = subst sub info.r' in
        let ty = subst_bnd sub info.ty in
        let tm = subst sub info.tm in
        Coe {r; r'; ty; tm}

      | HCom info ->
        let r = subst sub info.r in
        let r' = subst sub info.r' in
        let ty = subst sub info.ty in
        let cap = subst sub info.cap in
        let sys = subst_comp_sys sub info.sys in
        HCom {r; r'; ty; cap; sys}

      | FCom info ->
        let r = subst sub info.r in
        let r' = subst sub info.r' in
        let cap = subst sub info.cap in
        let sys = subst_comp_sys sub info.sys in
        FCom {r; r'; cap; sys}

      | Com info ->
        let r = subst sub info.r in
        let r' = subst sub info.r' in
        let ty = subst_bnd sub info.ty in
        let cap = subst sub info.cap in
        let sys = subst_comp_sys sub info.sys in
        Com {r; r'; ty; cap; sys}

      | Up t ->
        Up (subst sub t)

      | Pi (dom, cod) ->
        Pi (subst sub dom, subst_bnd sub cod)

      | Sg (dom, cod) ->
        Sg (subst sub dom, subst_bnd sub cod)

      | Ext (NB (nms, (cod, sys))) ->
        let sub' = liftn (List.length nms) sub in
        Ext (NB (nms, (subst sub' cod, subst_ext_sys sub' sys)))

      | Rst info ->
        let ty = subst sub info.ty in
        let sys = subst_ext_sys sub info.sys in
        Rst {ty; sys}

      | V info ->
        let r = subst sub info.r in
        let ty0 = subst sub info.ty0 in
        let ty1 = subst sub info.ty1 in
        let equiv = subst sub info.equiv in
        V {r; ty0; ty1; equiv}

      | If info ->
        let mot = subst_bnd sub info.mot in
        let scrut = subst sub info.scrut in
        let tcase = subst sub info.tcase in
        let fcase = subst sub info.fcase in
        If {mot; scrut; tcase; fcase}

      | VProj info ->
        let r = subst sub info.r in
        let tm = subst sub info.tm in
        let ty0 = subst sub info.ty0 in
        let ty1 = subst sub info.ty1 in
        let equiv = subst sub info.equiv in
        VProj {r; tm; ty0; ty1; equiv}

      | Lam bnd ->
        Lam (subst_bnd sub bnd)

      | ExtLam bnd ->
        ExtLam (subst_nbnd sub bnd)

      | Cons (t0, t1) ->
        Cons (subst sub t0, subst sub t1)

      | Let (t, bnd) ->
        Let (subst sub t, subst_bnd sub bnd)

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

(* TODO: double check that this is correct *)
and proj sub ix : inf f =
  match sub with
  | Id ->
    Var ix
  | Proj ->
    Var (ix + 1)
  | Sub (sub, t) ->
    if ix = 0 then unleash t else proj sub (ix - 1)
  | Cmp (sub1, sub0) ->
    substf sub1 @@ proj sub0 ix

and unleash : type x. x t -> x f =
  fun node ->
    let con = substf !node.subst !node.con in
    node := {!node with con; subst = Id};
    con



let up t = make @@ Up t
let lam nm t = make @@ Lam (B (nm, t))
let ext_lam nms t = make @@ ExtLam (NB (nms, t))
let pi nm dom cod = make @@ Pi (dom, B (nm, cod))
let sg nm dom cod = make @@ Sg (dom, B (nm, cod))
let let_ nm t0 t1 = make @@ Let (t0, B (nm, t1))
let cons t0 t1 = make @@ Cons (t0, t1)
let univ ~kind ~lvl = make @@ Univ {kind; lvl}
let car t = make @@ Car t
let cdr t = make @@ Cdr t

let rec pp : type a. a t Pretty.t =
  fun env fmt tm ->
    match unleash tm with
    | Var i ->
      Uuseg_string.pp_utf_8 fmt @@
      Pretty.Env.var i env

    | Global nm ->
      Uuseg_string.pp_utf_8 fmt nm

    | Down {ty; tm} ->
      Format.fprintf fmt "@[<1>(%a@ %a@ %a)@]" Uuseg_string.pp_utf_8 "▷" (pp env) ty (pp env) tm

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

    | FunApp (tm0, tm1) ->
      Format.fprintf fmt "@[<1>(%a@ %a)@]" (pp env) tm0 (pp env) tm1

    | ExtApp (tm, tms) ->
      Format.fprintf fmt "@[<1>(%s %a@ %a)@]" "@" (pp env) tm (pp_terms env) tms

    | Car tm ->
      Format.fprintf fmt "@[<1>(car@ %a)@]" (pp env) tm

    | Cdr tm ->
      Format.fprintf fmt "@[<1>(cdr@ %a)@]" (pp env) tm

    | VProj {r; tm; _} ->
      (* TODO *)
      Format.fprintf fmt "@[<1>(vproj %a@ %a)@]" (pp env) r (pp env) tm

    | Up tm ->
      pp env fmt tm

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

    | Coe {r; r'; ty = B (nm, ty); tm} ->
      let x, env' = Pretty.Env.bind nm env in
      Format.fprintf fmt "@[<1>(coe %a %a@ [%a] %a@ %a)@]" (pp env) r (pp env) r' Uuseg_string.pp_utf_8 x (pp env') ty (pp env) tm

    | HCom {r; r'; ty; cap; sys} ->
      Format.fprintf fmt "@[<1>(hcom %a %a@ %a@ %a@ @[%a@])@]" (pp env) r (pp env) r' (pp env) ty (pp env) cap (pp_bsys env) sys

    | FCom {r; r'; cap; sys} ->
      Format.fprintf fmt "@[<1>(fcom %a %a@ %a@ @[%a@])@]" (pp env) r (pp env) r' (pp env) cap (pp_bsys env) sys

    | Com {r; r'; ty = B (nm, ty); cap; sys} ->
      let x, _env' = Pretty.Env.bind nm env in
      Format.fprintf fmt "@[<1>(com %a %a@ [%a] %a@ %a@ @[%a@])@]" (pp env) r (pp env) r' Uuseg_string.pp_utf_8 x (pp env) ty (pp env) cap (pp_bsys env) sys

    | If {mot = B (nm, mot); scrut; tcase; fcase} ->
      let x, env' = Pretty.Env.bind nm env in
      Format.fprintf fmt "@[<1>(if@ [%a] %a@ %a %a %a)@]" Uuseg_string.pp_utf_8 x (pp env') mot (pp env) scrut (pp env) tcase (pp env) fcase

    | Cons (tm0, tm1) ->
      Format.fprintf fmt "@[<1>(cons@ %a@ %a)@]" (pp env) tm0 (pp env) tm1

    | Let (tm0, B (nm, tm1)) ->
      let x, env' = Pretty.Env.bind nm env in
      Format.fprintf fmt "@[<1>(let@ @[<1>[%a %a]@] %a)@]" Uuseg_string.pp_utf_8 x (pp env) tm0 (pp env') tm1

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
      (up @@ make @@ FunApp (subst Proj f, up @@ var 0))
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
      ~f:(var 1)
      ~x:(up @@ var 0)
end
