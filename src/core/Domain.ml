open RedBasis open Bwd
include DomainData

let rec make : con -> value =
  fun con ->
    Node {con; action = I.idn}

and make_later ty =
  let tclo = TickCloConst ty in
  make @@ Later tclo

let clo_name (Clo {bnd = Tm.B (nm, _); _}) =
  nm

let nclo_names (NClo {nbnd = Tm.NB (nms, _); _}) =
  nms

let rec pp_env_cell fmt =
  function
  | `Val v ->
    pp_value fmt v
  | `Dim r ->
    I.pp fmt r
  | `Tick _ ->
    Format.fprintf fmt "<tick>"

and pp_env fmt =
  let pp_sep fmt () = Format.fprintf fmt ", " in
  Format.pp_print_list ~pp_sep pp_env_cell fmt


and pp_con fmt : con -> unit =
  function
  | Up up ->
    Format.fprintf fmt "%a" pp_neu up.neu
  | Lam clo ->
    Format.fprintf fmt "@[<1>(λ@ %a)@]" pp_clo clo
  | ExtLam abs ->
    Format.fprintf fmt "@[<1>(λ@ %a)@]" pp_abs abs
  | CoRThunk face ->
    Format.fprintf fmt "@[<1>{%a}@]" pp_val_face face
  | S1 ->
    Format.fprintf fmt "S1"
  | Base ->
    Format.fprintf fmt "base"
  | Loop _x ->
    Format.fprintf fmt "<loop>"
  | Pi {dom; cod} ->
    Format.fprintf fmt "@[<1>(Π@ %a@ %a)@]" pp_value dom pp_clo cod
  | Sg {dom; cod} ->
    Format.fprintf fmt "@[<1>(Σ@ %a@ %a)@]" pp_value dom pp_clo cod
  | Ext abs ->
    Format.fprintf fmt "@[<1>(#@ %a)@]" pp_ext_abs abs
  | Rst {ty; sys} ->
    Format.fprintf fmt "@[<1>(restrict@ %a@ %a)@]" pp_value ty pp_val_sys sys
  | CoR face ->
    Format.fprintf fmt "@[<1>(corestrict@ %a)@]" pp_val_face face
  | Univ {kind; lvl} ->
    Format.fprintf fmt "@[<1>(U@ %a %a)@]" Kind.pp kind Lvl.pp lvl
  | Cons (v0, v1) ->
    Format.fprintf fmt "@[<1>(pair@ %a %a)@]" pp_value v0 pp_value v1
  | V info ->
    Format.fprintf fmt "@[<1>(V@ %a@ %a@ %a@ %a)]" Name.pp info.x pp_value info.ty0 pp_value info.ty1 pp_value info.equiv
  | VIn info ->
    Format.fprintf fmt "@[<1>(Vin@ %a@ %a@ %a)]" Name.pp info.x pp_value info.el0 pp_value info.el1
  | Coe info ->
    let r, r' = Dir.unleash info.dir in
    Format.fprintf fmt "@[<1>(coe %a %a@ %a@ %a)@]" I.pp r I.pp r' pp_abs info.abs pp_value info.el
  | HCom info ->
    let r, r' = Dir.unleash info.dir in
    Format.fprintf fmt "@[<1>(hcom %a %a %a@ %a@ %a)@]" I.pp r I.pp r' pp_value info.ty pp_value info.cap pp_comp_sys info.sys
  | GHCom _ ->
    Format.fprintf fmt "<ghcom>"
  | FHCom _ ->
    Format.fprintf fmt "<fhcom>"
  | Box _ ->
    Format.fprintf fmt "<box>"
  | LblTy {lbl; args; ty} ->
    begin
      match args with
      | [] ->
        Format.fprintf fmt "{%a : %a}"
          Uuseg_string.pp_utf_8 lbl
          pp_value ty
      | _ ->
        Format.fprintf fmt "{%a %a : %a}"
          Uuseg_string.pp_utf_8 lbl
          pp_nfs args
          pp_value ty
    end
  | LblRet v ->
    Format.fprintf fmt "@[<1>(ret %a)@]" pp_value v
  | Later _clo ->
    Format.fprintf fmt "<later>"
  | Next _clo ->
    Format.fprintf fmt "<next>"
  | DFix _ ->
    Format.fprintf fmt "<dfix>"
  | DFixLine _ ->
    Format.fprintf fmt "<dfix-line>"
  | BoxModality _ ->
    Format.fprintf fmt "<box-modality>"
  | Shut _ ->
    Format.fprintf fmt "<shut>"
  | Data _ ->
    Format.fprintf fmt "<data>"
  | Intro info ->
    Format.fprintf fmt "@[<hv1>(%a %a %a)@]"
      Uuseg_string.pp_utf_8 info.clbl
      pp_values info.args
      pp_dims info.rs


and pp_value fmt value =
  let Node node = value in
  if node.action = I.idn then
    pp_con fmt node.con
  else
    Format.fprintf fmt "@[<hv1>@[<hv1>(%a)@]<%a>@]"
      pp_con node.con I.pp_action node.action


and pp_abs fmt =
  IAbs.pp pp_value fmt

and pp_names fmt xs =
  let pp_sep fmt () = Format.fprintf fmt " " in
  Format.pp_print_list ~pp_sep Name.pp fmt (Bwd.to_list xs)

and pp_ext_abs fmt =
  let pp_ext_body fmt (ty, sys) =
    Format.fprintf fmt "%a@ %a"
      pp_value ty pp_val_sys sys
  in
  IAbs.pp pp_ext_body fmt

and pp_val_sys : type x. Format.formatter -> (x, value) face list -> unit =
  fun fmt ->
    let pp_sep fmt () = Format.fprintf fmt "@ " in
    Format.pp_print_list ~pp_sep pp_val_face fmt

and pp_val_face : type x. _ -> (x, value) face -> unit =
  fun fmt ->
    function
    | Face.True (r0, r1, v) ->
      Format.fprintf fmt "@[<1>[!%a=%a@ %a]@]" I.pp r0 I.pp r1 pp_value v
    | Face.False (r0, r1) ->
      Format.fprintf fmt "@[<1>[%a/=%a]@]" I.pp r0 I.pp r1
    | Face.Indet (p, v) ->
      let r0, r1 = Eq.unleash p in
      Format.fprintf fmt "@[<1>[?%a=%a %a]@]" I.pp r0 I.pp r1 pp_value v

and pp_comp_sys : type x. Format.formatter -> (x, abs) face list -> unit =
  fun fmt ->
    let pp_sep fmt () = Format.fprintf fmt "@ " in
    Format.pp_print_list ~pp_sep pp_comp_face fmt

and pp_comp_face : type x. _ -> (x, abs) face -> unit =
  fun fmt ->
    function
    | Face.True (r0, r1, v) ->
      Format.fprintf fmt "@[<1>[!%a=%a@ %a]@]" I.pp r0 I.pp r1 pp_abs v
    | Face.False (r0, r1) ->
      Format.fprintf fmt "@[<1>[%a/=%a]@]" I.pp r0 I.pp r1
    | Face.Indet (p, v) ->
      let r0, r1 = Eq.unleash p in
      Format.fprintf fmt "@[<1>[?%a=%a %a]@]" I.pp r0 I.pp r1 pp_abs v

and pp_clo fmt (Clo clo) =
  let Tm.B (_, tm) = clo.bnd in
  Format.fprintf fmt "<clo %a & %a>" Tm.pp0 tm pp_env clo.rho.cells

and pp_nclo fmt (NClo clo) =
  let Tm.NB (_, tm) = clo.nbnd in
  Format.fprintf fmt "<clo %a & %a>" Tm.pp0 tm pp_env clo.rho.cells

and pp_neu fmt neu =
  match neu with
  | Lvl (None, i) ->
    Format.fprintf fmt "#%i" i

  | Lvl (Some x, _) ->
    Uuseg_string.pp_utf_8 fmt x

  | NHCom info ->
    let r, r' = Dir.unleash info.dir in
    Format.fprintf fmt "@[<1>(hcom %a %a@ %a@ %a@ %a)@]" I.pp r I.pp r' pp_value info.ty pp_neu info.cap pp_comp_sys info.sys

  | FunApp (neu, arg) ->
    Format.fprintf fmt "@[<1>(%a@ %a)@]" pp_neu neu pp_value arg.el

  | ExtApp (neu, args) ->
    Format.fprintf fmt "@[<1>(%s@ %a@ %a)@]" "@" pp_neu neu pp_dims args

  | Car neu ->
    Format.fprintf fmt "@[<1>(car %a)@]" pp_neu neu

  | Cdr neu ->
    Format.fprintf fmt "@[<1>(cdr %a)@]" pp_neu neu

  | Var {name; _} ->
    Name.pp fmt name

  | Meta {name; _} ->
    Name.pp fmt name

  | S1Rec _ ->
    Format.fprintf fmt "<S1-rec>"

  | Elim _ ->
    Format.fprintf fmt "<elim>"

  | Cap _ ->
    Format.fprintf fmt "<cap>"

  | VProj _ ->
    Format.fprintf fmt "<vproj>"

  | LblCall neu ->
    Format.fprintf fmt "@[<1>(call %a)@]" pp_neu neu

  | CoRForce neu ->
    Format.fprintf fmt "@[<1>(! %a)@]" pp_neu neu

  | Prev _ ->
    Format.fprintf fmt "<prev>"

  | Fix _ ->
    Format.fprintf fmt "<fix>"

  | FixLine _ ->
    Format.fprintf fmt "<fix-line>"

  | Open _ ->
    Format.fprintf fmt "<open>"


and pp_nf fmt nf =
  pp_value fmt nf.el

and pp_nfs fmt nfs =
  let pp_sep fmt () = Format.fprintf fmt " " in
  Format.pp_print_list ~pp_sep pp_nf fmt nfs

and pp_values fmt els =
  let pp_sep fmt () = Format.fprintf fmt " " in
  Format.pp_print_list ~pp_sep pp_value fmt els

and pp_dims fmt rs =
  let pp_sep fmt () = Format.fprintf fmt " " in
  Format.pp_print_list ~pp_sep I.pp fmt rs

module type Sort = Sort.S

module Value : Sort with type t = value with type 'a m = 'a =
struct
  type 'a m = 'a
  type t = value

  let act : I.action -> value -> value =
    fun phi (Node node) ->
      Node {node with action = I.cmp phi node.action}
end

exception ProjAbs of abs
exception ProjVal of value

module Abs = IAbs.M (Value)
module ValFace = Face.M (Value)
module AbsFace = Face.M (Abs)

let force_abs_face face =
  match face with
  | Face.True (_, _, abs) ->
    raise @@ ProjAbs abs
  | Face.False _ -> None
  | Face.Indet (xi, abs) ->
    Some (Face.Indet (xi, abs))

let force_val_face (face : val_face) =
  match face with
  | Face.True (_, _, v) ->
    raise @@ ProjVal v
  | Face.False _ -> None
  | Face.Indet (xi, v) ->
    Some (Face.Indet (xi, v))

let force_val_sys sys =
  try
    `Ok (Option.filter_map force_val_face sys)
  with
  | ProjVal v ->
    `Proj v

let force_abs_sys sys =
  try
    `Ok (Option.filter_map force_abs_face sys)
  with
  | ProjAbs abs ->
    `Proj abs

module CompSys :
sig
  include Sort
    with type t = comp_sys
    with type 'a m = [`Ok of comp_sys | `Proj of abs]
  val forall : I.atom -> t -> t
  val forallm : I.atom -> t m -> t m
end =
struct
  type t = comp_sys
  type 'a m = [`Ok of comp_sys | `Proj of abs]

  exception Proj of abs

  let rec act_aux phi (sys : t) =
    match sys with
    | [] -> []
    | face :: sys ->
      match AbsFace.act phi face with
      | Face.True (_, _, abs) ->
        raise @@ Proj abs
      | Face.False _ ->
        act_aux phi sys
      | Face.Indet (p, t) ->
        Face.Indet (p, t) :: act_aux phi sys

  let act phi sys =
    try `Ok (act_aux phi sys)
    with
    | Proj abs ->
      `Proj abs

  (* note that these functions do not commute with `make`
   * if there is a face with equation `x=x` where `x` is
   * the dimension. *)
  let forall x sys =
    List.filter (fun f -> Face.forall x f = `Keep) sys

  let forallm x msys =
    match msys with
    | `Ok sys -> `Ok (forall x sys)
    | `Proj abs -> `Proj abs

end

(* TODO merge this with CompSys *)
module BoxSys :
sig
  include Sort
    with type t = box_sys
    with type 'a m = [`Ok of box_sys | `Proj of value]
end =
struct
  type t = box_sys
  type 'a m = [`Ok of box_sys | `Proj of value]

  exception Proj of value

  let rec act_aux phi (sys : t) =
    match sys with
    | [] -> []
    | face :: sys ->
      match ValFace.act phi face with
      | Face.True (_, _, value) ->
        raise @@ Proj value
      | Face.False _ ->
        act_aux phi sys
      | Face.Indet (p, t) ->
        Face.Indet (p, t) :: act_aux phi sys

  let act phi sys =
    try `Ok (act_aux phi sys)
    with
    | Proj value ->
      `Proj value
end

module ValSys :
sig
  include Sort
    with type t = val_sys
    with type 'a m = 'a

  val from_rigid : rigid_val_sys -> t
  val forall : I.atom -> t -> t
end =
struct
  type t = val_sys
  type 'a m = 'a

  let act phi =
    List.map (ValFace.act phi)

  let from_rigid sys =
    let face : rigid_val_face -> val_face =
      function
      | Face.Indet (p, a) ->
        Face.Indet (p, a)
    in
    List.map face sys

  (* note that these functions do not commute with `make`
   * if there is a face with equation `x=x` where `x` is
   * the dimension. *)
  let forall x sys =
    List.filter (fun f -> Face.forall x f = `Keep) sys
end

module ExtAbs : IAbs.S with type el = value * val_sys =
  IAbs.M (Sort.Prod (Value) (ValSys))


module Env :
sig
  include Sort.S
    with type t = env
    with type 'a m = 'a
  val emp : env
  val clear_locals : env -> env
  val push : env_el -> env -> env
  val push_many : env_el list -> env -> env
  val act_env_el : I.action -> env_el -> env_el
end =
struct
  type t = env
  type 'a m = 'a

  let emp = {cells = []; global = I.idn}

  let clear_locals rho =
    {rho with cells = []}

  let push el {cells; global} =
    {cells = el :: cells; global}

  let push_many els {cells; global} =
    {cells = els @ cells; global}

  let act_env_el phi =
    function
    | `Val v ->
      `Val (Value.act phi v)
    | `Dim x ->
      `Dim (I.act phi x)
    | `Tick tck ->
      `Tick tck

  let act phi {cells; global} =
    {cells = List.map (act_env_el phi) cells;
     global = I.cmp phi global}
end

module Clo : Sort with type t = clo with type 'a m = 'a =
struct
  type t = clo
  type 'a m = 'a

  let act phi clo =
    match clo with
    | Clo info ->
      Clo {info with rho = Env.act phi info.rho}
end

module TickClo : Sort with type t = tick_clo with type 'a m = 'a =
struct
  type t = tick_clo
  type 'a m = 'a

  let act phi clo =
    match clo with
    | TickClo info ->
      TickClo {info with rho = Env.act phi info.rho}
    | TickCloConst v ->
      TickCloConst (Value.act phi v)
end

module NClo : Sort with type t = nclo with type 'a m = 'a =
struct
  type t = nclo
  type 'a m = 'a

  let act phi clo =
    match clo with
    | NClo info ->
      NClo {info with rho = Env.act phi info.rho}
end
