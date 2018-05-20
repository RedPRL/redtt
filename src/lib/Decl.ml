type t =
  | Define of {name : string; info : Tm.info; args : TmUtil.tele; body : Tm.chk Tm.t }

type document = t list

module Typing = Typing.M (struct let globals = GlobalCx.emp end)

module V = Val.M (GlobalCx.M (struct let globals = GlobalCx.emp end))
module LocalCx = LocalCx.M (V)

let decl_name dcl =
  match dcl with
  | Define {name; _} ->
    name

let rec tele_to_multibind tele bdy =
  match tele with
  | TmUtil.TEnd _ ->
    TmUtil.MBEnd bdy

  | TmUtil.TCons (nm, _, tele) ->
    TmUtil.MBConsVar (nm, tele_to_multibind tele bdy)

let to_inf decl =
  match decl with
  | Define {info; args; body; _} ->
    let ty = TmUtil.pi_from_tele (Some info) args in
    let tm = TmUtil.lam_from_multibind (Some info) @@ tele_to_multibind args body in
    Tm.make @@ Tm.Down {ty; tm}


let rec check_document decls =
  let rec go cx decls =
    match decls with
    | [] ->
      ()

    | decl :: decls ->
      let cx' = check_decl cx decl in
      go cx' decls
  in go LocalCx.emp decls

and check_decl cx decl =
  match decl with
  | Define {info; args; body} ->
    let ty = TmUtil.pi_from_tele (Some info) args in
    let tm = TmUtil.lam_from_multibind (Some info) @@ tele_to_multibind args body in
    let inf = Tm.make @@ Tm.Down {ty; tm} in
    let vty = Typing.infer cx inf in
    let el = LocalCx.eval cx tm in
    let tm' = LocalCx.quote cx ~ty:vty el in
    let nm = Some (decl_name decl) in
    let ppenv = LocalCx.ppenv cx in
    Format.fprintf
      Format.std_formatter
      "@[<v 0>%a@, : @[%a@]@, %a @[%a@]@, %a @[%a@]@]@,@."
      (Uuseg_string.pp_utf_8)
      (decl_name decl)
      (Tm.pp ppenv) ty
      (Uuseg_string.pp_utf_8)
      "▷"
      (Tm.pp ppenv) tm
      (Uuseg_string.pp_utf_8)
      "↡"
      (Tm.pp ppenv) tm';
    LocalCx.def cx ~nm ~ty:vty ~el
