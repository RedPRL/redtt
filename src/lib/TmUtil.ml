module Make (X : sig exception Error end) =
struct
  open X

  let make_node start stop con =
    Tm.into_info (start, stop) @@ con

  type tele =
    | TCons of Tm.chk Tm.t * tele
    | TEnd of Tm.chk Tm.t

  type 'a multibind = 
    | MBCons of 'a multibind
    | MBEnd of 'a

  let rec pi_from_tele start stop tele =
    match tele with
    | TEnd ty -> ty
    | TCons (ty, tele) ->
      Tm.into_info (start, stop) @@
      Tm.Pi (ty, Tm.B (pi_from_tele start stop tele))

  let rec sg_from_tele start stop tele =
    match tele with
    | TEnd ty -> ty
    | TCons (ty, tele) ->
      Tm.into_info (start, stop) @@
      Tm.Pi (ty, Tm.B (sg_from_tele start stop tele))

  let rec lam_from_multibind start stop mb =
    match mb with
    | MBEnd bdy -> bdy
    | MBCons mb ->
      Tm.into_info (start, stop) @@
      Tm.Lam (Tm.B (lam_from_multibind start stop mb))

  let rec ext_from_multibind start stop mb = 
    match mb with
    | MBCons (MBEnd (ty, sys)) ->
      Tm.into_info (start, stop) @@
      Tm.Ext (Tm.B (ty, sys))

    | MBCons mb ->
      Tm.into_info (start, stop) @@
      Tm.Ext (Tm.B (ext_from_multibind start stop mb, []))

    | MBEnd _ ->
      raise Error


  let rec make_multi_funapp start stop fn rest =
    match rest with
    | [] -> 
      fn
    | arg :: rest ->
      let fn' = make_multi_funapp start stop fn rest in
      make_node start stop @@ Tm.FunApp (fn', arg)

  let rec make_multi_extapp start stop fn rest =
    match rest with
    | [] -> 
      fn
    | arg :: rest ->
      let fn' = make_multi_funapp start stop fn rest in
      make_node start stop @@ Tm.ExtApp (fn', arg)

  let make_dim_const start stop i =
    match i with
    | 0 -> make_node start stop Tm.Dim0
    | 1 -> make_node start stop Tm.Dim1
    | _ -> raise Error

end