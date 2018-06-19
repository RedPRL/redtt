open RedBasis.Bwd
open BwdNotation

type tm = Tm.tm
type ty = Tm.tm

type twin = [`Only | `TwinL | `TwinR]

type 'a decl =
  | Hole of [`Rigid | `Flex]
  | Defn of [`Transparent | `Opaque] * 'a
  | Guess of {ty : 'a; tm : 'a}

type status =
  | Blocked
  | Active

type ('a, 'b) equation =
  {ty0 : ty;
   tm0 : 'a;
   ty1 : ty;
   tm1 : 'b}

type 'a param =
  [ `I
  | `P of 'a
  | `Tw of 'a * 'a
  | `R of 'a * 'a
  ]

type params = (Name.t * ty param) bwd

type 'a bind = B of string option * 'a

type problem =
  | Unify of (tm, tm) equation
  | Subtype of {ty0 : ty; ty1 : ty}
  | All of ty param * problem bind

type entry =
  | E of Name.t * ty * tm decl
  | Q of status * problem

let eqn_open_var k x tw q =
  let twl, twr =
    match tw with
    | `P -> `Only, `Only
    | `Tw -> `TwinL, `TwinR
  in
  let ty0 = Tm.open_var k x (fun _ -> twl) q.ty0 in
  let ty1 = Tm.open_var k x (fun _ -> twr) q.ty1 in
  let tm0 = Tm.open_var k x (fun _ -> twl) q.tm0 in
  let tm1 = Tm.open_var k x (fun _ -> twr) q.tm1 in
  {ty0; ty1; tm0; tm1}

let rec eqn_close_var x tw k q =
  let twl, twr =
    match tw with
    | `P -> `Only, `Only
    | `Tw -> `TwinL, `TwinR
  in
  let ty0 = Tm.close_var x (fun _ -> twl) k q.ty0 in
  let ty1 = Tm.close_var x (fun _ -> twr) k q.ty1 in
  let tm0 = Tm.close_var x (fun _ -> twl) k q.tm0 in
  let tm1 = Tm.close_var x (fun _ -> twr) k q.tm1 in
  {ty0; ty1; tm0; tm1}

let param_open_var k x =
  function
  | `I ->
    `I
  | `P ty ->
    `P (Tm.open_var k x (fun tw -> tw) ty)
  | `Tw (ty0, ty1) ->
    `Tw (Tm.open_var k x (fun tw -> tw) ty0, Tm.open_var k x (fun tw -> tw) ty1)
  | `R (r0, r1) ->
    `R (Tm.open_var k x (fun tw -> tw) r0, Tm.open_var k x (fun tw -> tw) r1)


let param_close_var x k =
  function
  | `I ->
    `I
  | `P ty ->
    `P (Tm.close_var x (fun tw -> tw) k ty)
  | `Tw (ty0, ty1) ->
    `Tw (Tm.close_var x (fun tw -> tw) k ty0, Tm.close_var x (fun tw -> tw) k ty1)
  | `R (r0, r1) ->
    `R (Tm.close_var x (fun tw -> tw) k r0, Tm.close_var x (fun tw -> tw) k r1)

let rec prob_open_var k x tw =
  function
  | Unify q ->
    Unify (eqn_open_var k x tw q)
  | Subtype q ->
    let ty0 = Tm.open_var k x (fun tw -> tw) q.ty0 in
    let ty1 = Tm.open_var k x (fun tw -> tw) q.ty1 in
    Subtype {ty0; ty1}
  | All (p, B (nm, prob)) ->
    All (param_open_var k x p, B (nm, prob_open_var (k + 1) x tw prob))

let rec prob_close_var x tw k =
  function
  | Unify q ->
    Unify (eqn_close_var x tw k q)
  | Subtype q ->
    let ty0 = Tm.close_var x (fun tw -> tw) k q.ty0 in
    let ty1 = Tm.close_var x (fun tw -> tw) k q.ty1 in
    Subtype {ty0; ty1}
  | All (p, B (nm, prob)) ->
    All (param_close_var x k p, B (nm, prob_close_var x tw (k + 1) prob))

let bind x param probx =
  let tw = match param with `Tw _ -> `Tw | _ -> `P in
  B (Name.name x, prob_close_var x tw 0 probx)


let unbind_with x param (B (_, prob)) =
  match param with
  | `Tw _ ->
    prob_open_var 0 x `Tw prob
  | _ ->
    prob_open_var 0 x `P prob

let unbind param (B (nm, prob)) =
  let x = Name.named nm in
  x,
  match param with
  | `Tw _ ->
    prob_open_var 0 x `Tw prob
  | _ ->
    prob_open_var 0 x `P prob


let pp_equation fmt q =
  if q.ty0 = q.ty1 then
    Format.fprintf fmt "@[<1>@[<1>%a@]@ %a@ @[<1>%a@ :@ %a@]@]"
      Tm.pp0 q.tm0
      Uuseg_string.pp_utf_8 "≐"
      Tm.pp0 q.tm1
      Tm.pp0 q.ty1
  else
    Format.fprintf fmt "@[<1>@[<1>%a@ :@ %a@]@ %a@ @[<1>%a@ :@ %a@]@]"
      Tm.pp0 q.tm0
      Tm.pp0 q.ty0
      Uuseg_string.pp_utf_8 "≐"
      Tm.pp0 q.tm1
      Tm.pp0 q.ty1

let pp_atomic_problem fmt =
  function
  | `Unify q ->
    pp_equation fmt q
  | `Subtype (ty0, ty1) ->
    Format.fprintf fmt "@[<1>%a %a %a@]"
      Tm.pp0 ty0
      Uuseg_string.pp_utf_8 "≼"
      Tm.pp0 ty1

let pp_param fmt =
  function
  | `I ->
    Format.fprintf fmt "dim"
  | `P ty ->
    Tm.pp0 fmt ty
  | `Tw (ty0, ty1) ->
    Format.fprintf fmt "%a %a %a"
      Tm.pp0 ty0
      Uuseg_string.pp_utf_8 "‡"
      Tm.pp0 ty1
  | `R (r0, r1) ->
    Format.fprintf fmt "%a = %a"
      Tm.pp0 r0
      Tm.pp0 r1


let pp_param_cell fmt (x, param) =
  match param with
  | `P ty ->
    Format.fprintf fmt "@[<1>%a : %a@]"
      Name.pp x
      Tm.pp0 ty

  | `Tw (ty0, ty1) ->
    Format.fprintf fmt "@[<1>%a : %a %a %a@]"
      Name.pp x
      Uuseg_string.pp_utf_8 "‡"
      Tm.pp0 ty0
      Tm.pp0 ty1

  | `I ->
    Format.fprintf fmt "@[<1>%a : dim@]"
      Name.pp x

  | `R (r0, r1) ->
    Format.fprintf fmt "@[<1>%a = %a@]"
      Tm.pp0 r0
      Tm.pp0 r1

let rec pp_params fmt =
  function
  | Emp ->
    ()

  | Snoc (Emp, (x, cell)) ->
    pp_param_cell fmt (x, cell)

  | Snoc (tele, (x, cell)) ->
    Format.fprintf fmt "%a,@,%a"
      pp_params tele
      pp_param_cell (x, cell)


let unfurl_problem prob =
  let rec go tele =
    function
    | Unify q ->
      tele, `Unify q
    | Subtype q ->
      tele, `Subtype (q.ty0, q.ty1)
    | All (prm, prob) ->
      let x, probx = unbind prm prob in
      go (tele #< (x, prm)) probx
  in
  go Emp prob

let inst_with_vars xs prob =
  let rec go xs prob =
    match xs, prob with
    | [], Unify q ->
      `Unify q
    | [], Subtype q ->
      `Subtype (q.ty0, q.ty1)
    | x :: xs, All (prm, prob) ->
      let probx = unbind_with x prm prob in
      go xs probx
    | _ -> failwith "unbind_with_vars"
  in
  try
    Some (go xs prob)
  with
  | _ ->
    None

let rec pp_problem fmt prob =
  let tele, q = unfurl_problem prob in
  Format.fprintf fmt "@[<v>@[<v>%a@]@,%a %a@]"
    pp_params tele
    Uuseg_string.pp_utf_8 "⊢"
    pp_atomic_problem q


let pp_entry fmt =
  function
  | E (x, ty, Hole _) ->
    Format.fprintf fmt "?%a@ :@ %a"
      Name.pp x
      Tm.pp0 ty

  | E (x, ty, Defn (`Transparent, tm)) ->
    Format.fprintf fmt "!%a@ : %a@ = %a"
      Name.pp x
      Tm.pp0 ty
      Tm.pp0 tm

  | E (x, ty, Defn (`Opaque, _)) ->
    Format.fprintf fmt "!%a@ : %a@ = <opaque>"
      Name.pp x
      Tm.pp0 ty

  | E (x, ty, Guess _) ->
    Format.fprintf fmt "?%a@ :@ %a"
      Name.pp x
      Tm.pp0 ty

  | Q (_, prob) ->
    Format.fprintf fmt "%a"
      pp_problem prob

module Subst = GlobalEnv

module type DevSort =
sig
  include Occurs.S
  val pp : t Pretty.t0
  val subst : Subst.t -> t -> t
end

let subst_tm sub ~ty tm =
  let module T = Typing.M (struct let globals = sub end) in
  let vty = T.Cx.eval T.Cx.emp ty in
  let el = T.Cx.eval T.Cx.emp tm in
  T.Cx.quote T.Cx.emp ~ty:vty el

let subst_decl sub ~ty =
  function
  | Hole x ->
    Hole x
  | Defn (opacity, t) ->
    Defn (opacity, subst_tm sub ~ty t)
  | Guess info ->
    let univ = Tm.univ ~lvl:Lvl.Omega ~kind:Kind.Pre in
    let ty' = subst_tm sub ~ty:univ info.ty in
    Guess {ty = ty'; tm = subst_tm sub ~ty:ty' info.tm}

let subst_equation sub q =
  let univ = Tm.univ ~kind:Kind.Pre ~lvl:Lvl.Omega in
  let ty0 = subst_tm sub ~ty:univ q.ty0 in
  let ty1 = subst_tm sub ~ty:univ q.ty1 in
  let tm0 = subst_tm sub ~ty:ty0 q.tm0 in
  let tm1 = subst_tm sub ~ty:ty1 q.tm1 in
  {ty0; ty1; tm0; tm1}

let subst_param sub =
  let univ = Tm.univ ~kind:Kind.Pre ~lvl:Lvl.Omega in
  function
  | `I ->
    `I, sub
  | `P ty ->
    `P (subst_tm sub ~ty:univ ty), sub
  | `Tw (ty0, ty1) ->
    `Tw (subst_tm sub ~ty:univ ty0, subst_tm sub ~ty:univ ty1), sub
  | `R (r0, r1) ->
    (* TODO: ??? *)
    `R (r0, r1), GlobalEnv.restrict r0 r1 sub

let rec subst_problem sub =
  let univ = Tm.univ ~kind:Kind.Pre ~lvl:Lvl.Omega in
  function
  | Unify q ->
    Unify (subst_equation sub q)
  | Subtype q ->
    let ty0 = subst_tm sub ~ty:univ q.ty0 in
    let ty1 = subst_tm sub ~ty:univ q.ty1 in
    Subtype {ty0; ty1}
  | All (param, prob) ->
    let param', sub' = subst_param sub param in
    let x, probx = unbind param prob in
    begin
      match param with
      | `P ty ->
        let sub'' = GlobalEnv.ext sub' x @@ `P {ty; sys = []}  in
        let probx' = subst_problem sub'' probx in
        let prob' = bind x param' probx' in
        All (param', prob')
      | `Tw (ty0, ty1) ->
        let sub'' = GlobalEnv.ext sub' x @@ `Tw ({ty = ty0; sys = []}, {ty = ty1; sys = []}) in
        let probx' = subst_problem sub'' probx in
        let prob' = bind x param' probx' in
        All (param', prob')
      | `I ->
        let probx' = subst_problem sub' probx in
        let prob' = bind x param' probx' in
        All (param', prob')
      | `R (_, _) ->
        let probx' = subst_problem sub' probx in
        let prob' = bind x param' probx' in
        All (param', prob')
    end

let subst_entry sub =
  function
  | E (x, ty, decl) ->
    let univ = Tm.univ ~kind:Kind.Pre ~lvl:Lvl.Omega in
    E (x, subst_tm sub ~ty:univ ty, subst_decl sub ~ty decl)
  | Q (s, p) ->
    let p' = subst_problem sub p in
    let s' = if p = p' then s else Active in
    Q (s', p')


module Param =
struct
  type t = ty param
  let pp = pp_param

  let free fl =
    function
    | `I -> Occurs.Set.empty
    | `P ty -> Tm.free fl ty
    | `Tw (ty0, ty1) ->
      Occurs.Set.union (Tm.free fl ty0) (Tm.free fl ty1)
    | `R (r0, r1) ->
      Occurs.Set.union (Tm.free fl r0) (Tm.free fl r1)

  let subst sub p = fst @@ subst_param sub p
end

module Params = Occurs.Bwd (Param)

module Decl =
struct
  type t = Tm.tm decl
  let free fl =
    function
    | Hole _ -> Occurs.Set.empty
    | Defn (`Transparent, t) -> Tm.free fl t
    | Defn (`Opaque, _) -> Occurs.Set.empty
    | Guess {tm; _} -> Tm.free fl tm
end


module Equation =
struct
  type t = (tm, tm) equation
  let pp = pp_equation

  let free fl {ty0; tm0; ty1; tm1} =
    let sets =
      [ Tm.free fl ty0;
        Tm.free fl tm0;
        Tm.free fl ty1;
        Tm.free fl tm1 ]
    in List.fold_right Occurs.Set.union sets Occurs.Set.empty

  let sym q =
    {ty0 = q.ty1; tm0 = q.tm1; ty1 = q.ty0; tm1 = q.tm0}

  let subst = subst_equation
end

module Problem =
struct
  type t = problem

  let pp = pp_problem

  let rec free fl =
    function
    | Unify q ->
      Equation.free fl q
    | Subtype q ->
      Occurs.Set.union (Tm.free fl q.ty0) (Tm.free fl q.ty1)
    | All (p, B (_, prob)) ->
      Occurs.Set.union (Param.free fl p) (free fl prob)

  let eqn ~ty0 ~tm0 ~ty1 ~tm1 =
    Unify {ty0; tm0; ty1; tm1}

  let all x ty prob =
    All (`P ty, bind x (`P ty) prob)

  let rec all_dims xs prob =
    match xs with
    | [] -> prob
    | x :: xs ->
      All (`I, bind x `I @@ all_dims xs prob)

  let all_twins x ty0 ty1 prob =
    All (`Tw (ty0, ty1), bind x (`Tw (ty0, ty1)) prob)

  let subst = subst_problem
end

module Entry =
struct
  type t = entry

  let pp = pp_entry

  let free fl =
    function
    | E (_, _, d) ->
      Decl.free fl d
    | Q (_, p) ->
      Problem.free fl p

  let subst = subst_entry
end

module Entries : Occurs.S with type t = entry list =
  Occurs.List (Entry)
