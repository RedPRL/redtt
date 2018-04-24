type t =
  | Define of {name : string; info : Tm.info; args : TmUtil.tele; body : Tm.chk Tm.t }

type document = t list

let decl_name dcl = 
  match dcl with
  | Define {name; _} ->
    name

let rec tele_to_multibind tele bdy = 
  match tele with
  | TmUtil.TEnd _ -> 
    TmUtil.MBEnd bdy

  | TmUtil.TCons (nm, _, tele) -> 
    TmUtil.MBCons (nm, tele_to_multibind tele bdy)

let to_inf decl = 
  match decl with
  | Define {info; args; body; _} ->
    let ty = TmUtil.pi_from_tele (Some info) args in
    let tm = TmUtil.lam_from_multibind (Some info) @@ tele_to_multibind args body in
    Tm.into @@ Tm.Down {ty; tm}


let rec check_document cx decls = 
  match decls with
  | [] ->
    ()

  | decl :: decls ->
    let cx' = check_decl cx decl in
    check_document cx' decls

and check_decl cx decl = 
  match decl with
  | Define {info; args; body; name} ->
    let ty = TmUtil.pi_from_tele (Some info) args in
    let tm = TmUtil.lam_from_multibind (Some info) @@ tele_to_multibind args body in
    let inf = Tm.into @@ Tm.Down {ty; tm} in
    let ty = Typing.infer ~mcx:MCx.emp ~cx ~tm:inf in
    let el = Val.eval (MEnv.empty, LCx.env cx) tm in
    let nm = Some (decl_name decl) in
    let ppenv = LCx.ppenv cx in
    Format.fprintf Format.std_formatter "> %a@.@." (Tm.pp ppenv) inf;
    LCx.def cx ~nm ty el