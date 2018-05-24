open RedBasis

type 'a bnd = B of string option * 'a
type 'a nbnd = NB of string option list * 'a

type chk = [`Chk]
type head = [`Head]

type info = Lexing.position * Lexing.position

type _ f =
  | FCom : {r : chk t; r' : chk t; cap : chk t; sys : chk t bnd system} -> chk f

  | Univ : {kind : Kind.t; lvl : Lvl.t} -> chk f
  | Pi : chk t * chk t bnd -> chk f
  | Ext : (chk t * chk t system) nbnd -> chk f
  | Rst : {ty : chk t; sys : chk t system} -> chk f
  | Sg : chk t * chk t bnd -> chk f

  | V : {r : chk t; ty0 : chk t; ty1 : chk t; equiv : chk t} -> chk f

  | Bool : chk f
  | Tt : chk f
  | Ff : chk f

  | Lam : chk t bnd -> chk f
  | ExtLam : chk t nbnd -> chk f

  | Cons : chk t * chk t -> chk f
  | Dim0 : chk f
  | Dim1 : chk f

  (* Labelled types from Epigram *)
  | LblTy : {lbl : string; args : (chk t * chk t) list; ty : chk t} -> chk f
  | LblRet : chk t -> chk f

  | Ref : Name.t -> head f
  | Ix : int -> head f
  | Down : {ty : chk t; tm : chk t} -> head f
  | Coe : {r : chk t; r' : chk t; ty : chk t bnd; tm : chk t} -> head f
  | HCom : {r : chk t; r' : chk t; ty : chk t; cap : chk t; sys : chk t bnd system} -> head f
  | Com : {r : chk t; r' : chk t; ty : chk t bnd; cap : chk t; sys : chk t bnd system} -> head f

  | Let : cmd * chk t bnd -> chk f
  | MuStar : cmd -> chk f

and spine = frame list

and frame =
  | Car
  | Cdr
  | FunApp of chk t
  | ExtApp of chk t list
  | If of {mot : chk t bnd; tcase : chk t; fcase : chk t}
  | VProj of {r : chk t; ty0 : chk t; ty1 : chk t; equiv : chk t}
  | LblCall

and cmd = Cut of head t * spine

and subst =
  | Id
  | Proj
  | Sub of subst * cmd
  | Cmp of subst * subst

and 'a node = {info : info option; con : 'a f}
and 'a t = 'a node
and 'a face = chk t * chk t * 'a option
and 'a system = 'a face list


let make tf = {info = None; con = tf}
let with_info info tf = {info = info; con = tf}
let info node = !node.info


let ($$) hd stk : cmd =
  Cut (make hd, stk)

let var i : cmd =
  Ix i $$ []

let lift sub =
  Sub (Cmp (sub, Proj), var 0)

let rec liftn n sub =
  match n with
  | 0 -> sub
  | _ -> liftn (n - 1) @@ lift sub

let inst0 t = Sub (Id, t)


let rec subst_chk (sub : subst) {info; con} =
  {info; con = subst_chk_f sub con}

and subst_chk_f (sub : subst) =
  function
  | (Dim0 | Dim1 | Univ _ | Bool | Tt | Ff) as con ->
    con

  | FCom info ->
    let r = subst_chk sub info.r in
    let r' = subst_chk sub info.r' in
    let cap = subst_chk sub info.cap in
    let sys = subst_comp_sys sub info.sys in
    FCom {r; r'; cap; sys}

  | MuStar cmd ->
    MuStar (subst_cmd sub cmd)

  | Pi (dom, cod) ->
    Pi (subst_chk sub dom, subst_bnd sub cod)

  | Sg (dom, cod) ->
    Sg (subst_chk sub dom, subst_bnd sub cod)

  | Ext ebnd ->
    Ext (subst_ext_bnd sub ebnd)

  | Rst info ->
    let ty = subst_chk sub info.ty in
    let sys = subst_tm_sys sub info.sys in
    Rst {ty; sys}

  | V info ->
    let r = subst_chk sub info.r in
    let ty0 = subst_chk sub info.ty0 in
    let ty1 = subst_chk sub info.ty1 in
    let equiv = subst_chk sub info.equiv in
    V {r; ty0; ty1; equiv}

  | Lam bnd ->
    Lam (subst_bnd sub bnd)

  | ExtLam nbnd ->
    ExtLam (subst_nbnd sub nbnd)

  | Cons (t0, t1) ->
    Cons (subst_chk sub t0, subst_chk sub t1)

  | LblTy info ->
    let args = List.map (fun (ty, tm) -> subst_chk sub ty, subst_chk sub tm) info.args in
    let ty = subst_chk sub info.ty in
    LblTy {info with args; ty}

  | LblRet t ->
    LblRet (subst_chk sub t)

  | Let (cmd, bnd) ->
    Let (subst_cmd sub cmd, subst_bnd sub bnd)

and subst_tm_sys sub  =
  List.map (subst_tm_face sub)

and subst_tm_face sub (r, r', otm) =
  subst_chk sub r, subst_chk sub r', Option.map (subst_chk sub) otm


and subst_cmd sub =
  function Cut (head, spine) ->
    let Cut (head', spine') = subst_head sub head in
    let spine'' = subst_spine sub spine in
    Cut (head', spine' @ spine'')

and subst_spine sub spine =
  List.map (subst_frame sub) spine

and subst_frame sub frame : frame =
  match frame with
  | (Car | Cdr | LblCall) ->
    frame
  | FunApp t ->
    FunApp (subst_chk sub t)
  | ExtApp ts ->
    ExtApp (List.map (subst_chk sub) ts)
  | If info ->
    let mot = subst_bnd sub info.mot in
    let tcase = subst_chk sub info.tcase in
    let fcase = subst_chk sub info.fcase in
    If {mot; tcase; fcase}
  | VProj info ->
    let r = subst_chk sub info.r in
    let ty0 = subst_chk sub info.ty0 in
    let ty1 = subst_chk sub info.ty1 in
    let equiv = subst_chk sub info.equiv in
    VProj {r; ty0; ty1; equiv}

and subst_head sub head : cmd =
  match head.con with
  | Ix i ->
    subst_ix sub i

  | Ref a ->
    Cut (with_info head.info (Ref a), [])

  | Down info ->
    let ty = subst_chk sub info.ty in
    let tm = subst_chk sub info.tm in
    Cut (with_info head.info (Down {ty; tm}), [])

  | HCom info ->
    let r = subst_chk sub info.r in
    let r' = subst_chk sub info.r' in
    let ty = subst_chk sub info.ty in
    let cap = subst_chk sub info.cap in
    let sys = subst_comp_sys sub info.sys in
    Cut (with_info head.info (HCom {r; r'; ty; cap; sys}), [])

  | Coe info ->
    let r = subst_chk sub info.r in
    let r' = subst_chk sub info.r' in
    let ty = subst_bnd sub info.ty in
    let tm = subst_chk sub info.tm in
    Cut (with_info head.info (Coe {r; r'; ty; tm}), [])

  | Com info ->
    let r = subst_chk sub info.r in
    let r' = subst_chk sub info.r' in
    let ty = subst_bnd sub info.ty in
    let cap = subst_chk sub info.cap in
    let sys = subst_comp_sys sub info.sys in
    Cut (with_info head.info (Com {r; r'; ty; cap; sys}), [])

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
  B (nm, subst_chk (lift sub) t)

and subst_nbnd sub bnd =
  let NB (nms, t) = bnd in
  NB (nms, subst_chk (liftn (List.length nms) sub) t)

and subst_ext_bnd sub ebnd =
  let NB (nms, (ty, sys)) = ebnd in
  let sub' = liftn (List.length nms) sub in
  let ty' = subst_chk sub' ty in
  let sys' = subst_tm_sys sub' sys in
  NB (nms, (ty', sys'))


and subst_ext_sys sub sys =
  List.map (subst_ext_face sub) sys

and subst_ext_face sub (r, r', otm) =
  let r = subst_chk sub r in
  let r' = subst_chk sub r' in
  let otm = Option.map (subst_chk sub) otm in
  r, r', otm

and subst_comp_face sub (r, r', obnd) =
  let r = subst_chk sub r in
  let r' = subst_chk sub r' in
  let obnd = Option.map (subst_bnd sub) obnd in
  r, r', obnd

and subst_comp_sys sub sys =
  List.map (subst_comp_face sub) sys


let unleash : type x. x t -> x f =
  fun node ->
    node.con


let close_var : type x. Name.t -> int -> x t -> x t =
  fun a ->
    let rec go : type x. int -> x t -> x t =
      fun k tm ->
        with_info tm.info @@
        match tm.con with
        | Univ _ -> tm.con
        | Bool -> tm.con
        | Tt -> tm.con
        | Ff -> tm.con
        | Dim0 -> tm.con
        | Dim1 -> tm.con
        | Lam bnd ->
          Lam (go_bnd k bnd)
        | Pi (dom, cod) ->
          Pi (go k dom, go_bnd k cod)
        | Sg (dom, cod) ->
          Sg (go k dom, go_bnd k cod)
        | Ext ebnd ->
          Ext (go_ext_bnd k ebnd)
        | Rst info ->
          let ty = go k info.ty in
          let sys = go_tm_sys k info.sys in
          Rst {ty; sys}
        | FCom info ->
          let r = go k info.r in
          let r' = go k info.r' in
          let cap = go k info.cap in
          let sys = go_comp_sys k info.sys in
          FCom {r; r'; cap; sys}
        | V info ->
          let r = go k info.r in
          let ty0 = go k info.ty0 in
          let ty1 = go k info.ty1 in
          let equiv = go k info.equiv in
          V {r; ty0; ty1; equiv}
        | ExtLam nbnd ->
          ExtLam (go_nbnd k nbnd)
        | Cons (t0, t1) ->
          Cons (go k t0, go k t1)
        | LblTy info ->
          let args = List.map (fun (t0, t1) -> go k t0, go k t1) info.args in
          let ty = go k info.ty in
          LblTy {info with args; ty}
        | LblRet t ->
          LblRet (go k t)
        | Ref b ->
          if a = b then Ix k else tm.con
        | Ix _ -> tm.con
        | Down info ->
          let ty = go k info.ty in
          let tm = go k info.tm in
          Down {ty; tm}
        | Coe info ->
          let r = go k info.r in
          let r' = go k info.r' in
          let ty = go_bnd k info.ty in
          let tm = go k info.tm in
          Coe {r; r'; ty; tm}
        | HCom info ->
          let r = go k info.r in
          let r' = go k info.r' in
          let ty = go k info.ty in
          let cap = go k info.cap in
          let sys = go_comp_sys k info.sys in
          HCom {r; r'; ty; cap; sys}
        | Com info ->
          let r = go k info.r in
          let r' = go k info.r' in
          let ty = go_bnd k info.ty in
          let cap = go k info.cap in
          let sys = go_comp_sys k info.sys in
          Com {r; r'; ty; cap; sys}
        | MuStar cmd ->
          MuStar (go_cmd k cmd)
        | Let _ -> failwith ""

    and go_cmd k =
      function Cut (hd, sp) ->
        Cut (go k hd, go_spine k sp)

    and go_spine k =
      List.map (go_frame k)

    and go_frame k =
      function
      | (Car | Cdr | LblCall) as frm -> frm
      | FunApp t ->
        FunApp (go k t)
      | ExtApp ts ->
        ExtApp (List.map (go k) ts)
      | If info ->
        let mot = go_bnd k info.mot in
        let tcase = go k info.tcase in
        let fcase = go k info.fcase in
        If {mot; tcase; fcase}
      | VProj info ->
        let r = go k info.r in
        let ty0 = go k info.ty0 in
        let ty1 = go k info.ty1 in
        let equiv = go k info.equiv in
        VProj {r; ty0; ty1; equiv}

    and go_bnd : type x. int -> x t bnd -> x t bnd =
      fun k (B (nm, t)) ->
        B (nm, go (k + 1) t)

    and go_comp_sys k sys =
      List.map (go_comp_face k) sys

    and go_comp_face k (r, r', obnd) =
      go k r, go k r', Option.map (go_bnd k) obnd

    and go_ext_bnd k (NB (nms, (ty, sys))) =
      let k' = k + List.length nms in
      NB (nms, (go k' ty, go_tm_sys k' sys))

    and go_nbnd k (NB (nms, t)) =
      let k' = k + List.length nms in
      NB (nms, go k' t)

    and go_tm_sys k sys =
      List.map (go_tm_face k) sys

    and go_tm_face k (r, r', otm) =
      go k r, go k r', Option.map (go k) otm
    in go

let open_var : type x. int -> Name.t -> chk t -> chk t =
  fun k a t ->
    subst_chk (liftn k @@ inst0 @@ Cut (make @@ Ref a, [])) t

let rec pp : type x. x t Pretty.t =
  fun env fmt tm ->
    match tm.con with
    | Ix i ->
      Uuseg_string.pp_utf_8 fmt @@
      Pretty.Env.var i env

    | Ref nm ->
      Name.pp fmt nm

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

    | MuStar cmd ->
      pp_cmd env fmt cmd

and pp_cmd env fmt =
  function Cut (hd, sp) ->
    let rec go fmt sp =
      match sp with
      | [] -> pp env fmt hd
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

and pp_terms : type x. x t list Pretty.t =
  fun env fmt ts ->
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

let up cmd = make @@ MuStar cmd

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
    subst_chk Proj ty1

  let times ty0 ty1 =
    sg None ty0 @@
    subst_chk Proj ty1

  let path ty tm0 tm1 =
    let ty' = subst_chk Proj ty in
    let face0 = up (var 0), make Dim0, Some (subst_chk Proj tm0) in
    let face1 = up (var 0), make Dim1, Some (subst_chk Proj tm1) in
    let sys = [face0; face1] in
    make @@ Ext (NB ([None], (ty', sys)))

  let fiber ~ty0 ~ty1 ~f ~x =
    sg None ty0 @@
    path
      (subst_chk Proj ty1)
      (up @@ (Ix 0 $$ [FunApp (subst_chk Proj f)]))
      (subst_chk Proj x)

  let proj2 = Cmp (Proj, Proj)

  let is_contr ty =
    sg None ty @@
    pi None (subst_chk Proj ty) @@
    path
      (subst_chk proj2 ty)
      (up @@ var 0)
      (up @@ var 1)

  let equiv ty0 ty1 =
    sg None (arr ty0 ty1) @@
    pi None (subst_chk Proj ty1) @@
    is_contr @@
    fiber
      ~ty0:(subst_chk proj2 ty0)
      ~ty1:(subst_chk proj2 ty1)
      ~f:(up @@ var 1)
      ~x:(up @@ var 0)
end
