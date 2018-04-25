type 'a bnd = B of string option * 'a

type chk = [`Chk]
type inf = [`Inf]

type info = Lexing.position * Lexing.position

type _ f =
  | Var : int -> inf f
  | Car : inf t -> inf f
  | Cdr : inf t -> inf f
  | FunApp : inf t * chk t -> inf f
  | ExtApp : inf t * chk t -> inf f

  | Down : {ty : chk t; tm : chk t} -> inf f
  | Coe : {dim0 : chk t; dim1 : chk t; ty : chk t bnd; tm : chk t} -> inf f
  | HCom : {dim0 : chk t; dim1 : chk t; ty : chk t; cap : chk t; sys : chk t bnd system} -> inf f
  | Com : {dim0 : chk t; dim1 : chk t; ty : chk t bnd; cap : chk t; sys : chk t bnd system} -> inf f

  | Up : inf t -> chk f

  | Univ : Lvl.t -> chk f
  | Pi : chk t * chk t bnd -> chk f
  | Ext : (chk t * chk t system) bnd -> chk f
  | Sg : chk t * chk t bnd -> chk f
  | Interval : chk f

  | Bool : chk f
  | Tt : chk f
  | Ff : chk f
  | If : {mot : chk t bnd; scrut : inf t; tcase : chk t; fcase : chk t} -> inf f

  | Lam : chk t bnd -> chk f
  | Cons : chk t * chk t -> chk f
  | Dim0 : chk f
  | Dim1 : chk f

  | Let : inf t * chk t bnd -> chk f
  | Meta : Symbol.t * subst -> inf f

and subst =
  | Id
  | Proj
  | Sub of subst * inf t
  | Cmp of subst * subst

and 'a node = {info : info option; con : 'a f}
and 'a t = 'a node
and 'a tube = chk t * chk t * 'a option
and 'a system = 'a tube list

let into tf = {info = None; con = tf}
let into_info info tf = {info = info; con = tf}
let info node = node.info

let out node = node.con

let var i = into @@ Var i
let inst0 t = Sub (Id, t)

let meta hole sub = into @@ Meta (hole, sub)
let up t = into @@ Up t
let lam nm t = into @@ Lam (B (nm, t))
let pi nm dom cod = into @@ Pi (dom, B (nm, cod))
let sg nm dom cod = into @@ Sg (dom, B (nm, cod))
let let_ nm t0 t1 = into @@ Let (t0, B (nm, t1))
let cons t0 t1 = into @@ Cons (t0, t1)
let univ lvl = into @@ Univ lvl
let car t = into @@ Car t
let cdr t = into @@ Cdr t
let meta sym subst = into @@ Meta (sym, subst)

let rec pp : type a. a t Pretty.t =
  fun env fmt tm ->
    match out tm with
    | Var i ->
      Format.fprintf fmt "%s" @@
      Pretty.Env.var i env

    | Down {ty; tm} ->
      Format.fprintf fmt "@[<1>(▷@ %a@ %a)@]" (pp env) ty (pp env) tm

    | Pi (dom, B (nm, cod)) ->
      let x, env' = Pretty.Env.bind nm env in
      Format.fprintf fmt "@[<1>(→ [%s : %a]@ %a)@]" x (pp env) dom (pp env') cod

    | Sg (dom, B (nm, cod)) ->
      let x, env' = Pretty.Env.bind nm env in
      Format.fprintf fmt "@[<1>(× [%s : %a]@ %a)@]" x (pp env) dom (pp env') cod

    | Ext (B (nm, (cod, sys))) ->
      let x, env' = Pretty.Env.bind nm env in
      begin
        match sys with
        | [] ->
          Format.fprintf fmt "@[<1>(# [%s]@ %a)@]" x (pp env') cod
        | _ ->
          Format.fprintf fmt "@[<1>(# [%s]@ %a@ @[%a@])@]" x (pp env') cod (pp_sys env') sys
      end

    | Lam (B (nm, tm)) ->
      let x, env' = Pretty.Env.bind nm env in
      Format.fprintf fmt "@[<1>(λ [%s]@ %a)@]" x (pp env') tm

    | FunApp (tm0, tm1) ->
      Format.fprintf fmt "@[<1>(%a@ %a)@]" (pp env) tm0 (pp env) tm1

    | ExtApp (tm0, tm1) ->
      Format.fprintf fmt "@[<1>(%s %a@ %a)@]" "@" (pp env) tm0 (pp env) tm1

    | Car tm ->
      Format.fprintf fmt "@[<1>(car@ %a)@]" (pp env) tm

    | Cdr tm ->
      Format.fprintf fmt "@[<1>(cdr@ %a)@]" (pp env) tm

    | Up tm ->
      pp env fmt tm

    | Bool ->
      Format.fprintf fmt "bool"

    | Interval ->
      Format.fprintf fmt "dim"

    | Tt ->
      Format.fprintf fmt "tt"

    | Ff ->
      Format.fprintf fmt "ff"

    | Dim0 ->
      Format.fprintf fmt "0"

    | Dim1 ->
      Format.fprintf fmt "1"

    | Univ lvl ->
      Format.fprintf fmt "(U %a)" Lvl.pp lvl

    | Coe {dim0; dim1; ty = B (nm, ty); tm} ->
      let x, env' = Pretty.Env.bind nm env in
      Format.fprintf fmt "@[<1>(coe %a %a@ [%s] %a@ %a)@]" (pp env) dim0 (pp env) dim1 x (pp env') ty (pp env) tm

    | HCom {dim0; dim1; ty; cap; sys} ->
      Format.fprintf fmt "@[<1>(hcom %a %a@ %a@ %a@ @[%a@])@]" (pp env) dim0 (pp env) dim1 (pp env) ty (pp env) cap (pp_bsys env) sys

    | Com {dim0; dim1; ty = B (nm, ty); cap; sys} ->
      let x, _env' = Pretty.Env.bind nm env in
      Format.fprintf fmt "@[<1>(com %a %a@ [%s] %a@ %a@ @[%a@])@]" (pp env) dim0 (pp env) dim1 x (pp env) ty (pp env) cap (pp_bsys env) sys

    | If {mot = B (nm, mot); scrut; tcase; fcase} ->
      let x, env' = Pretty.Env.bind nm env in
      Format.fprintf fmt "@[<1>(if@ [%s] %a@ %a %a %a)@]" x (pp env') mot (pp env) scrut (pp env) tcase (pp env) fcase

    | Cons (tm0, tm1) ->
      Format.fprintf fmt "@[<1>(cons@ %a@ %a)@]" (pp env) tm0 (pp env) tm1

    | Let (tm0, B (nm, tm1)) ->
      let x, env' = Pretty.Env.bind nm env in
      Format.fprintf fmt "@[<1>(let@ @[<1>[%s %a]@] %a)@]" x (pp env) tm0 (pp env') tm1

    | Meta _ ->
      Format.fprintf fmt "<meta>"


and pp_sys env fmt sys =
  match sys with
  | [] ->
    ()

  | [tube] ->
    pp_tube env fmt tube

  | tube :: sys ->
    Format.fprintf fmt "%a@ %a" (pp_tube env) tube (pp_sys env) sys

and pp_bsys env fmt sys =
  match sys with
  | [] ->
    ()

  | [tube] ->
    pp_btube env fmt tube

  | tube :: sys ->
    Format.fprintf fmt "%a@ %a" (pp_btube env) tube (pp_bsys env) sys

and pp_tube env fmt tube =
  let dim0, dim1, otm = tube in
  match otm with
  | None ->
    Format.fprintf fmt "@[<1>[%a=%a@ -]@]" (pp env) dim0 (pp env) dim1

  | Some tm ->
    Format.fprintf fmt "@[<1>[%a=%a@ %a]@]" (pp env) dim0 (pp env) dim1 (pp env) tm

and pp_btube env fmt tube =
  let dim0, dim1, obnd = tube in
  match obnd with
  | None ->
    Format.fprintf fmt "@[<1>[%a=%a@ -]@]" (pp env) dim0 (pp env) dim1

  | Some (B (nm, tm)) ->
    let x, env' = Pretty.Env.bind nm env in
    Format.fprintf fmt "@[<1>[%a=%a@ [%s] %a]@]" (pp env) dim0 (pp env) dim1 x (pp env') tm
