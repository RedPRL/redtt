open RedBasis.Bwd

let make_node _start _stop con =
  Tm.make con

type tele =
  | TCons of string option * Tm.tm * tele
  | TEnd of Tm.tm

type 'a multibind =
  | MBConsVar of string option * 'a multibind
  | MBConsDims of string option list * 'a multibind
  | MBEnd of 'a

let rec pi_from_tele info tele =
  match tele with
  | TEnd ty -> ty
  | TCons (nm, ty, tele) ->
    Tm.pi nm ty @@
    pi_from_tele info tele

let rec sg_from_tele info tele =
  match tele with
  | TEnd ty -> ty
  | TCons (nm, ty, tele) ->
    Tm.sg nm ty @@
    sg_from_tele info tele

let rec lam_from_multibind info mb =
  match mb with
  | MBEnd bdy -> bdy
  | MBConsVar (nm, mb) ->
    Tm.lam nm @@
    lam_from_multibind info mb
  | MBConsDims (nms, mb) ->
    Tm.ext_lam (Bwd.from_list nms) @@
    lam_from_multibind info mb

let rec ext_from_multibind start stop mb =
  match mb with
  | MBConsDims (nms, MBEnd (ty, sys)) ->
    Tm.make @@ Tm.Ext (Tm.NB (Bwd.from_list nms, (ty, sys)))

  | MBConsDims (nms, mb) ->
    Tm.make @@ Tm.Ext (Tm.NB (Bwd.from_list nms, (ext_from_multibind start stop mb, [])))

  | _ ->
    failwith "ext_from_multibind"


let make_dim_const start stop i =
  match i with
  | 0 -> make_node start stop Tm.Dim0
  | 1 -> make_node start stop Tm.Dim1
  | _ -> failwith "make_dim_const"
