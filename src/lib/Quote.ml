open Val


module Env :
sig
  type t

  val len : t -> int

  val emp : t
  val make : int -> t
  val succ : t -> t
  val abs : t -> Symbol.t -> t

  val ix_of_lvl : int -> t -> int
  val ix_of_atom : Symbol.t -> t -> int
end =
struct
  module M = Map.Make (Symbol)
  type t = {n : int; atoms : int M.t}

  let len env =
    env.n

  let make n =
    {n; atoms = M.empty}

  let emp = make 0

  let succ env =
    {env with n = env.n + 1}

  let abs env x =
    {n = env.n + 1;
     atoms = M.add x env.n env.atoms}
  (* TODO: should that be env.n + 1? *)

  let ix_of_lvl l env =
    env.n - (l + 1)

  let ix_of_atom x env =
    try
      let lvl = M.find x env.atoms in
      ix_of_lvl lvl env
    with _ -> failwith "FUCK!!:"
end

type env = Env.t

let generic env ty =
  make @@ Up {ty = ty; neu = Lvl (Env.len env)}

let rec equate env ty el0 el1 =
  match unleash ty with
  | Pi {dom; cod} ->
    let var = generic env dom in
    let vcod = inst_clo cod var in
    let app0 = apply el0 var in
    let app1 = apply el1 var in
    Tm.lam None @@ equate (Env.succ env) vcod app0 app1


  | Sg {dom; cod} ->
    let el00 = car el0 in
    let el10 = car el1 in
    let q0 = equate env dom el00 el10 in
    let vcod = inst_clo cod el00 in
    let q1 = equate env vcod (cdr el0) (cdr el1) in
    Tm.cons q0 q1

  | Ext abs ->
    let x, (tyx, _) = ExtAbs.unleash abs in
    let r = Dim.named x in
    let app0 = ext_apply el0 r in
    let app1 = ext_apply el1 r in
    Tm.ext_lam None @@ equate (Env.abs env x) tyx app0 app1

  (* TODO: V type, in order to get eta law *)

  | _ ->
    match unleash el0, unleash el1 with
    | Univ lvl0, Univ lvl1 ->
      if lvl0 = lvl1 then
        Tm.univ lvl0
      else
        failwith "Expected equal universe levels"

    | Bool, Bool ->
      Tm.make Tm.Bool

    | Pi pi0, Pi pi1 ->
      let dom = equate env ty pi0.dom pi1.dom in
      let var = generic env pi0.dom in
      let vcod0 = inst_clo pi0.cod var in
      let vcod1 = inst_clo pi1.cod var in
      let cod = equate env ty vcod0 vcod1 in
      Tm.pi None dom cod

    | Sg sg0, Sg sg1 ->
      let dom = equate env ty sg0.dom sg1.dom in
      let var = generic env sg0.dom in
      let vcod0 = inst_clo sg0.cod var in
      let vcod1 = inst_clo sg1.cod var in
      let cod = equate env ty vcod0 vcod1 in
      Tm.sg None dom cod

    | Ext abs0, Ext abs1 ->
      let x, (ty0x, sys0x) = ExtAbs.unleash abs0 in
      let ty1x, sys1x = ExtAbs.inst abs1 @@ Dim.named x in
      let envx = Env.abs env x in
      let tyx = equate envx ty ty0x ty1x in
      let sysx = equate_val_sys envx ty0x sys0x sys1x in
      Tm.make @@ Tm.Ext (Tm.B (None, (tyx, sysx)))

    | Up up0, Up up1 ->
      Tm.up @@ equate_neu env up0.neu up1.neu

    | FCom fcom0, FCom fcom1 ->
      let tr, tr' = equate_star env fcom0.dir fcom1.dir in
      let cap = equate env ty fcom0.cap fcom1.cap in
      let sys = equate_comp_sys env ty fcom0.sys fcom1.sys in
      Tm.make @@ Tm.FCom {r = tr; r' = tr'; cap; sys}

    | HCom hcom0, HCom hcom1 ->
      let tr, tr' = equate_star env hcom0.dir hcom1.dir in
      let ty = equate_ty env hcom0.ty hcom1.ty in
      let cap = equate env hcom0.ty hcom0.cap hcom1.cap in
      let sys = equate_comp_sys env hcom0.ty hcom0.sys hcom1.sys in
      Tm.up @@ Tm.make @@ Tm.HCom {r = tr; r' = tr'; ty; cap; sys}

    | Coe coe0, Coe coe1 ->
      let tr, tr' = equate_star env coe0.dir coe1.dir in
      let univ = make @@ Univ Lvl.Omega in
      let bnd = equate_val_abs env univ coe0.abs coe1.abs in
      let tyr =
        let r, _ = DimStar.unleash coe0.dir in
        Abs.inst coe0.abs @@ r
      in
      let tm = equate env tyr coe0.el coe1.el in
      Tm.up @@ Tm.make @@ Tm.Coe {r = tr; r' = tr'; ty = bnd; tm}

    | _ ->
      failwith "equate"

and equate_neu env neu0 neu1 =
  match neu0, neu1 with
  | Lvl l0, Lvl l1 ->
    if l0 = l1 then
      Tm.var @@ Env.ix_of_lvl l0 env
    else
      failwith "equate_neu: expected equal de bruijn levels"

  | Car neu0, Car neu1 ->
    Tm.car @@ equate_neu env neu0 neu1

  | Cdr neu0, Cdr neu1 ->
    Tm.cdr @@ equate_neu env neu0 neu1

  | FunApp (neu0, nf0), FunApp (neu1, nf1) ->
    let t0 = equate_neu env neu0 neu1 in
    let t1 = equate env nf0.ty nf0.el nf1.el in
    Tm.make @@ Tm.FunApp (t0, t1)

  | ExtApp (neu0, _, r0), ExtApp (neu1, _, r1) ->
    let t = equate_neu env neu0 neu1 in
    let tr = equate_dim env r0 r1 in
    Tm.make @@ Tm.ExtApp (t, tr)

  | If if0, If if1 ->
    let var = generic env @@ make Bool in
    let vmot0 = inst_clo if0.mot var in
    let vmot1 = inst_clo if1.mot var in
    let mot = equate_ty (Env.succ env) vmot0 vmot1 in
    let scrut = equate_neu env if0.neu if1.neu in
    let vmot_tt = inst_clo if0.mot @@ make Tt in
    let vmot_ff = inst_clo if0.mot @@ make Ff in
    let tcase = equate env vmot_tt if0.tcase if1.tcase in
    let fcase = equate env vmot_ff if0.fcase if1.fcase in
    Tm.make @@ Tm.If {mot = Tm.B (None, mot); scrut; tcase; fcase}

  | VProj _vproj0, VProj _vproj1 ->
    (* let r0 = DimGeneric.unleash vproj0.x in *)
    (* let r1 = DimGeneric.unleash vproj1.x in *)
    (* let tr = equate_dim env r0 r1 in
       let tm = equate_neu env vproj0.neu vproj1.neu in
       let funty =
       let _, ty0, ty1, _ = unleash_v vproj0.vty in
       make @@ Pi {dom = ty0; cod = const_clo ty1}
       in
       let func = equate env funty vproj0.func vproj1.func in
       Tm.make @@ Tm.VProj {r = tr; tm; func} *)
    failwith "TODO"

  | _ -> failwith "equate_neu"

and equate_ty env ty0 ty1 : Tm.chk Tm.t =
  let univ = make @@ Univ Lvl.Omega in
  equate env univ ty0 ty1


and equate_val_sys env ty sys0 sys1 =
  try
    List.map2 (equate_val_face env ty) sys0 sys1
  with
  | Invalid_argument _ ->
    failwith "equate_val_sys length mismatch"

and equate_comp_sys env ty sys0 sys1 =
  try
    List.map2 (equate_comp_face env ty) sys0 sys1
  with
  | Invalid_argument _ ->
    failwith "equate_cmop_sys length mismatch"


and equate_val_face env ty face0 face1 =
  match face0, face1 with
  | Face.True (r0, r'0, v0), Face.True (r1, r'1, v1) ->
    let tr = equate_dim env r0 r1 in
    let tr' = equate_dim env r'0 r'1 in
    let t = equate env ty v0 v1 in
    tr, tr', Some t

  | Face.False p0, Face.False p1 ->
    let tr, tr' = equate_star env p0 p1 in
    tr, tr', None

  | Face.Indet (p0, v0), Face.Indet (p1, v1) ->
    let tr, tr' = equate_star env p0 p1 in
    let v = equate env ty v0 v1 in
    tr, tr', Some v

  | _ -> failwith "equate_val_face"

and equate_comp_face env ty face0 face1 =
  match face0, face1 with
  | Face.False p0, Face.False p1 ->
    let tr, tr' = equate_star env p0 p1 in
    tr, tr', None

  | Face.Indet (p0, abs0), Face.Indet (p1, abs1) ->
    let tr, tr' = equate_star env p0 p1 in
    let bnd = equate_val_abs env ty abs0 abs1 in
    tr, tr', Some bnd

  | _ -> failwith "equate_comp_face"

and equate_val_abs env ty abs0 abs1 =
  let x, v0x = Abs.unleash abs0 in
  let v1x = Abs.inst abs1 @@ Dim.named x in
  let envx = Env.abs env x in
  let tm = equate envx ty v0x v1x in
  Tm.B (None, tm)

and equate_star env p0 p1 =
  let r0, r'0 = DimStar.unleash p0 in
  let r1, r'1 = DimStar.unleash p1 in
  let tr = equate_dim env r0 r1 in
  let tr' = equate_dim env r'0 r'1 in
  tr, tr'

and equate_dim env r r' =
  match Dim.compare r r' with
  | Same ->
    quote_dim env r
  | _ ->
    failwith "Dimensions did not match"

and quote_dim env r =
  match Dim.unleash r with
  | Dim.Dim0 -> Tm.make Tm.Dim0
  | Dim.Dim1 -> Tm.make Tm.Dim1
  | Dim.Atom x ->
    let ix = Env.ix_of_atom x env in
    Tm.up @@ Tm.var ix

let equiv env ~ty el0 el1 =
  ignore @@ equate env ty el0 el1

let quote_nf env nf =
  equate env nf.ty nf.el nf.el

let quote_neu env neu =
  equate_neu env neu neu

let rec subtype env ty0 ty1 =
  match unleash ty0, unleash ty1 with
  | Pi pi0, Pi pi1 ->
    subtype env pi1.dom pi0.dom;
    let var = generic env pi0.dom in
    let vcod0 = inst_clo pi0.cod var in
    let vcod1 = inst_clo pi1.cod var in
    subtype env vcod0 vcod1

  | Sg sg0, Sg sg1 ->
    subtype env sg0.dom sg1.dom;
    let var = generic env sg0.dom in
    let vcod0 = inst_clo sg0.cod var in
    let vcod1 = inst_clo sg1.cod var in
    subtype env vcod0 vcod1

  | Ext abs0, Ext abs1 ->
    let x, (ty0x, sys0x) = ExtAbs.unleash abs0 in
    let ty1x, sys1x = ExtAbs.inst abs1 @@ Dim.named x in
    let envx = Env.abs env x in
    subtype envx ty0x ty1x;
    ignore @@ equate_val_sys envx ty0x sys0x sys1x

  | Univ lvl0, Univ lvl1 ->
    if lvl0 = lvl1 or Lvl.greater lvl1 lvl0 then
      ()
    else
      failwith "Universe level too big"

  | _ ->
    let univ = make @@ Univ Lvl.Omega in
    equiv env univ ty0 ty1
