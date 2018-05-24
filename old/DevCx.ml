open Dev

type t =
  | Emp
  | Ext of t * cell

let rec ppenv =
  function
  | Emp -> Pretty.Env.emp
  | Ext (cx, c) ->
    ppenv_cell (ppenv cx) c

let rec pp_cx_ env fmt =
  function
  | Emp -> env
  | Ext (Emp, c) ->
    pp_cell env fmt c;
    ppenv_cell env c
  | Ext (t, c) ->
    let env' = pp_cx_ env fmt t in
    Format.fprintf fmt "@,";
    pp_cell env' fmt c;
    ppenv_cell env' c

let pp_cx fmt cx =
  ignore @@ pp_cx_ Pretty.Env.emp fmt cx

let emp = Emp
let ext t c = Ext (t, c)

exception EmptyContext

let pop =
  function
  | Emp -> raise EmptyContext
  | Ext (cx, _) -> cx

let rec core sg =
  let module Sig = GlobalCx.M (struct let globals = sg end) in
  let module V = Val.M (Sig) in
  let module LocalCx = LocalCx.M (V) in
  let rec go dcx =
    match dcx with
    | Emp ->
      LocalCx.emp

    | Ext (dcx, c) ->
      let tcx = go dcx in
      begin
        match c with
        | Guess {ty; nm; _} ->
          let vty = LocalCx.eval tcx ty in
          fst @@ LocalCx.ext_ty tcx ~nm vty

        | Let {ty; nm; def} ->
          let vty = LocalCx.eval tcx ty in
          let vdef = LocalCx.eval tcx def in
          LocalCx.def tcx ~nm ~ty:vty ~el:vdef

        | Lam {ty; nm} ->
          let vty = LocalCx.eval tcx ty in
          fst @@ LocalCx.ext_ty tcx ~nm vty
      end
  in go

let rec skolemize dcx ~cod =
  let rec go i dcx (cod, args) =
    match dcx with
    | Emp ->
      cod, List.rev args
    | Ext (dcx, c) ->
      go (i + 1) dcx @@
      begin
        match c with
        | Guess {ty; nm; _} ->
          Tm.make @@ Tm.Pi (ty, Tm.B (nm, cod)), Tm.up (Tm.var i) :: args
        | Let {ty; def; _} ->
          let inf = Tm.make @@ Tm.Down {ty; tm = def} in
          Tm.subst (Tm.inst0 inf) cod, args
        | Lam {ty; nm} ->
          Tm.make @@ Tm.Pi (ty, Tm.B (nm, cod)), Tm.up (Tm.var i) :: args
      end
  in
  go 0 dcx (cod, [])
