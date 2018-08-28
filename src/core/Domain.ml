open RedBasis open Bwd open BwdNotation
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

and pp_env fmt env =
  let pp_sep fmt () = Format.fprintf fmt ", " in
  Format.pp_print_list ~pp_sep pp_env_cell fmt (Bwd.to_list env.cells)


and pp_con fmt : con -> unit =
  function
  | Up up ->
    begin
      match up.sys with
      | [] ->
        Format.fprintf fmt "@[<hv1>(up@ %a@ %a)@]" pp_value up.ty pp_neu up.neu
      | _ ->
        Format.fprintf fmt "@[<hv1>(up@ %a@ %a@ %a)@]" pp_value up.ty pp_neu up.neu pp_val_sys up.sys
    end
  | Lam clo ->
    Format.fprintf fmt "@[<1>(λ@ %a)@]" pp_clo clo
  | ExtLam abs ->
    Format.fprintf fmt "@[<1>(λ@ %a)@]" pp_abs abs
  | CoRThunk face ->
    Format.fprintf fmt "@[<1>{%a}@]" pp_val_face face
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
    Format.fprintf fmt "@[<1>(V@ %a@ %a@ %a@ %a)@]" Name.pp info.x pp_value info.ty0 pp_value info.ty1 pp_value info.equiv
  | VIn info ->
    Format.fprintf fmt "@[<1>(Vin@ %a@ %a@ %a)@]" Name.pp info.x pp_value info.el0 pp_value info.el1
  | Coe info ->
    let r, r' = Dir.unleash info.dir in
    Format.fprintf fmt "@[<1>(coe %a %a@ %a@ %a)@]" I.pp r I.pp r' pp_abs info.abs pp_value info.el
  | HCom info ->
    let r, r' = Dir.unleash info.dir in
    Format.fprintf fmt "@[<1>(hcom %a %a %a@ %a@ %a)@]" I.pp r I.pp r' pp_value info.ty pp_value info.cap pp_comp_sys info.sys
  | GHCom _ ->
    Format.fprintf fmt "<ghcom>"
  | FHCom info ->
    let r, r' = Dir.unleash info.dir in
    Format.fprintf fmt "@[<1>(fhcom %a %a@ %a@ %a)@]" I.pp r I.pp r' pp_value info.cap pp_comp_sys info.sys
  | Box info ->
    let r, r' = Dir.unleash info.dir in
    Format.fprintf fmt "@[<1>(box %a %a@ %a@ %a)@]" I.pp r I.pp r' pp_value info.cap pp_val_sys info.sys
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
  | Data lbl ->
    Uuseg_string.pp_utf_8 fmt lbl
  | Intro info ->
    Format.fprintf fmt "@[<hv1>(%a %a %a %a)@]"
      Uuseg_string.pp_utf_8 info.clbl
      pp_values info.const_args
      pp_values info.rec_args
      pp_dims info.rs


and pp_value fmt value =
  let Node node = value in
  if node.action = I.idn then
    pp_con fmt node.con
  else
    Format.fprintf fmt "@[<hv1>@[<hv1>%a@]@[<hv1><%a>@]@]"
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
      Format.fprintf fmt "@[<1>[!%a=%a@ %a]@]" I.pp r0 I.pp r1 pp_value (Lazy.force v)
    | Face.False (r0, r1) ->
      Format.fprintf fmt "@[<1>[%a/=%a]@]" I.pp r0 I.pp r1
    | Face.Indet (p, v) ->
      let r0, r1 = Eq.unleash p in
      Format.fprintf fmt "@[<1>[?%a=%a %a]@]" I.pp r0 I.pp r1 pp_value (Lazy.force v)

and pp_comp_sys : type x. Format.formatter -> (x, abs) face list -> unit =
  fun fmt ->
    let pp_sep fmt () = Format.fprintf fmt "@ " in
    Format.pp_print_list ~pp_sep pp_comp_face fmt

and pp_comp_face : type x. _ -> (x, abs) face -> unit =
  fun fmt ->
    function
    | Face.True (r0, r1, v) ->
      Format.fprintf fmt "@[<1>[!%a=%a@ %a]@]" I.pp r0 I.pp r1 pp_abs (Lazy.force v)
    | Face.False (r0, r1) ->
      Format.fprintf fmt "@[<1>[%a/=%a]@]" I.pp r0 I.pp r1
    | Face.Indet (p, v) ->
      let r0, r1 = Eq.unleash p in
      Format.fprintf fmt "@[<1>[?%a=%a %a]@]" I.pp r0 I.pp r1 pp_abs (Lazy.force v)

and pp_clo fmt (Clo clo) =
  let Tm.B (_, tm) = clo.bnd in
  Format.fprintf fmt "@[<hv1>(clo@ %a@ <:@ %a)@]" Tm.pp0 tm pp_env clo.rho

and pp_nclo fmt (NClo clo) =
  let Tm.NB (_, tm) = clo.nbnd in
  Format.fprintf fmt "@[<hv1>(clo@ %a@ <:@ %a)@]" Tm.pp0 tm pp_env clo.rho

and pp_neu fmt neu =
  match neu with
  | Lvl (None, i) ->
    Format.fprintf fmt "#%i" i

  | Lvl (Some x, _) ->
    Uuseg_string.pp_utf_8 fmt x

  | NHComAtType info ->
    let r, r' = Dir.unleash info.dir in
    Format.fprintf fmt "@[<1>(nhcom-type %a %a@ %a@ %a@ %a)@]" I.pp r I.pp r' pp_neu info.ty pp_value info.cap pp_comp_sys info.sys

  | NHComAtCap info ->
    let r, r' = Dir.unleash info.dir in
    Format.fprintf fmt "@[<1>(nhcom-cap %a %a@ %a@ %a@ %a)@]" I.pp r I.pp r' pp_value info.ty pp_neu info.cap pp_comp_sys info.sys

  | NCoe info ->
    let r, r' = Dir.unleash info.dir in
    Format.fprintf fmt "@[<1>(ncoe %a %a@ %a@ %a)@]" I.pp r I.pp r' pp_abs info.abs pp_neu info.neu

  | NCoeAtType info ->
    let r, r' = Dir.unleash info.dir in
    Format.fprintf fmt "@[<1>(ncoe %a %a@ %a@ %a)@]" I.pp r I.pp r' pp_abs info.abs pp_value info.el

  | FunApp (neu, arg) ->
    Format.fprintf fmt "@[<1>(%a@ %a)@]" pp_neu neu pp_value arg.el

  | ExtApp (neu, args) ->
    Format.fprintf fmt "@[<1>(%s@ %a@ %a)@]" "@" pp_neu neu pp_dims args

  | Car neu ->
    Format.fprintf fmt "@[<hv1>(car@ %a)@]" pp_neu neu

  | Cdr neu ->
    Format.fprintf fmt "@[<hv1>(cdr@ %a)@]" pp_neu neu

  | Var {name; _} ->
    Name.pp fmt name

  | Meta {name; _} ->
    Name.pp fmt name

  | Elim info ->
    Format.fprintf fmt "@[<hv1>(%a.elim@ %a@ %a@ %a)@]"
      Desc.pp_data_label info.dlbl
      pp_clo info.mot
      pp_neu info.neu
      pp_elim_clauses info.clauses

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

and pp_elim_clauses fmt clauses =
  let pp_sep fmt () = Format.fprintf fmt "@ " in
  Format.pp_print_list ~pp_sep pp_elim_clause fmt clauses

and pp_elim_clause fmt (clbl, nclo) =
  Format.fprintf fmt "@[<hv1>[%a@ %a]@]" Uuseg_string.pp_utf_8 clbl pp_nclo nclo

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


exception ProjAbs of abs
exception ProjVal of value

let force_abs_face face =
  match face with
  | Face.True (_, _, abs) ->
    raise @@ ProjAbs (Lazy.force abs)
  | Face.False _ -> None
  | Face.Indet (xi, abs) ->
    Some (Face.Indet (xi, abs))

let force_val_face (face : val_face) =
  match face with
  | Face.True (_, _, v) ->
    raise @@ ProjVal (Lazy.force v)
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






module type Sort = Sort.S

module rec Value : Sort with type t = value with type 'a m = 'a =
struct
  type 'a m = 'a
  type t = value

  let rec act : I.action -> value -> value =
    fun phi (Node node) ->
      try
        if node.action = I.idn then
          match node.con with
          | (Data _ | Univ _) -> Node node
          | Up {ty; neu; sys = []} ->
            begin
              make @@ Up {ty = act phi ty; neu = Neu.act phi neu; sys = []}
            end
          | _ ->
            Node {node with action = I.cmp phi node.action}
        else
          Node {node with action = I.cmp phi node.action}
      with
      | _ ->
        Node {node with action = I.cmp phi node.action}

end
and Neu : Sort with type t = neu with type 'a m = 'a =
struct
  type 'a m = 'a
  type t = neu

  exception TooMortal

  let rec act phi =
    function
    | NHComAtType info ->
      begin
        match Dir.act phi info.dir, CompSys.act phi info.sys with
        | `Ok dir, `Ok sys ->
          let univ = Value.act phi info.univ in
          let cap = Value.act phi info.cap in
          let ty = act phi info.ty in
          NHComAtType {dir; univ; ty; cap; sys}
        | _ ->
          raise TooMortal
      end

    | NHComAtCap info ->
      begin
        match Dir.act phi info.dir, CompSys.act phi info.sys with
        | `Ok dir, `Ok sys ->
          let ty = Value.act phi info.ty in
          let cap = act phi info.cap in
          NHComAtCap {dir; ty; cap; sys}
        | _ ->
          raise TooMortal
      end

    | NCoe info ->
      begin
        match Dir.act phi info.dir with
        | `Ok dir ->
          let abs = Abs.act phi info.abs in
          let neu = act phi info.neu in
          NCoe {dir; abs; neu}
        | _ ->
          raise TooMortal
      end

    | NCoeAtType info ->
      begin
        match Dir.act phi info.dir with
        | `Ok dir ->
          let abs = Abs.act phi info.abs in
          let el = Value.act phi info.el in
          NCoeAtType {dir; abs; el}
        | _ ->
          raise TooMortal
      end

    | VProj info ->
      begin
        match I.act phi @@ `Atom info.x with
        | `Atom y ->
          let ty0 = Value.act phi info.ty0 in
          let ty1 = Value.act phi info.ty1 in
          let equiv = Value.act phi info.equiv in
          let neu = act phi info.neu in
          VProj {x = y; neu; ty0; ty1; equiv}
        | _ ->
          raise TooMortal
      end

    | Cap info ->
      begin
        match Dir.act phi info.dir, CompSys.act phi info.sys with
        | `Ok dir, `Ok sys ->
          let ty = Value.act phi info.ty in
          let neu = act phi info.neu in
          Cap {dir; ty; neu; sys}
        | _ ->
          raise TooMortal
      end

    | ExtApp (neu, rs) ->
      let neu = act phi neu in
      let rs = List.map (I.act phi) rs in
      ExtApp (neu, rs)

    | FunApp (neu, arg) ->
      let neu = act phi neu in
      let arg = Nf.act phi arg in
      FunApp (neu, arg)

    | Car neu ->
      let neu = act phi neu in
      Car neu

    | Cdr neu ->
      let neu = act phi neu in
      Cdr neu

    | Elim info ->
      let mot = Clo.act phi info.mot in
      let go (lbl, nclo) = lbl, NClo.act phi nclo in
      let clauses = List.map go info.clauses in
      let neu = act phi info.neu in
      Elim {dlbl = info.dlbl; mot; neu; clauses}

    | LblCall neu ->
      let neu = act phi neu in
      LblCall neu

    | CoRForce neu ->
      let neu = act phi neu in
      CoRForce neu

    | (Lvl _ | Var _ | Meta _) as neu ->
      neu

    | Prev (tick, neu) ->
      let neu = act phi neu in
      Prev (tick, neu)

    | Fix (tick, ty, clo) ->
      let ty = Value.act phi ty in
      let clo = Clo.act phi clo in
      Fix (tick, ty, clo)

    | FixLine (x, tick, ty, clo) ->
      begin
        match I.act phi (`Atom x) with
        | `Atom y ->
          let ty = Value.act phi ty in
          let clo = Clo.act phi clo in
          FixLine (y, tick, ty, clo)
        | _ ->
          raise TooMortal
      end
end

and Nf : Sort with type t = nf with type 'a m = 'a =
struct
  type 'a m = 'a
  type t = nf
  let act phi nf =
    let ty = Value.act phi nf.ty in
    let el = Value.act phi nf.el in
    {ty; el}
end

and Abs : IAbs.S with type el = value = IAbs.M (Value)

and ValFace : Face.S with type body := value = Face.M (Value)

and AbsFace : Face.S with type body := abs = Face.M (Abs)

and CompSys :
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
        raise @@ Proj (Lazy.force abs)
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
and BoxSys :
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
        raise @@ Proj (Lazy.force value)
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

and ValSys :
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

and ExtAbs : IAbs.S with type el = value * val_sys =
  IAbs.M (Sort.Prod (Value) (ValSys))

and Env :
sig
  include Sort.S
    with type t = env
    with type 'a m = 'a
  val emp : env
  val clear_locals : env -> env
  val snoc : env -> env_el -> env
  val append : env -> env_el list -> env
  val act_env_el : I.action -> env_el -> env_el
end =
struct
  type t = env
  type 'a m = 'a

  let emp = {cells = Emp; global = I.idn}

  let clear_locals rho =
    {rho with cells = Emp}

  let snoc {cells; global} el =
    {cells = cells #< el; global}

  let append {cells; global} els =
    {cells = cells <>< els; global}

  let act_env_el phi =
    function
    | `Val v ->
      `Val (Value.act phi v)
    | `Dim x ->
      `Dim (I.act phi x)
    | `Tick tck ->
      `Tick tck

  let act phi {cells; global} =
    {cells = Bwd.map (act_env_el phi) cells;
     global = I.cmp phi global}
end

and Clo : Sort with type t = clo with type 'a m = 'a =
struct
  type t = clo
  type 'a m = 'a

  let act phi clo =
    match clo with
    | Clo info ->
      Clo {info with rho = Env.act phi info.rho}
end

and TickClo : Sort with type t = tick_clo with type 'a m = 'a =
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

and NClo : Sort with type t = nclo with type 'a m = 'a =
struct
  type t = nclo
  type 'a m = 'a

  let act phi clo =
    match clo with
    | NClo info ->
      NClo {info with rho = Env.act phi info.rho}
end
