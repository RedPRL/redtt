open RedBasis
open Bwd

module D = Dim
module Star = DimStar
module Gen = DimGeneric

type atom = Name.t
type dim = D.t
type star = Star.t
type gen = Gen.t

module R = Restriction
type rel = R.t

(* Notes: I have defined the semantic domain and evaluator in a fairly naive way, in order to avoid
   some confusing questions. It may not be that efficient! But it should be easier at this point to
   transform it make something efficient, since the code is currently simple-minded enough to
   think about. *)

type con =
  | Pi : {dom : value; cod : clo} -> con
  | Sg : {dom : value; cod : clo} -> con
  | Rst : {ty : value; sys : val_sys} -> con
  | CoR : val_face -> con
  | Ext : ext_abs -> con

  | Coe : {dir : star; abs : abs; el : value} -> con
  | HCom : {dir : star; ty : value; cap : value; sys : comp_sys} -> con
  | GHCom : {dir : star; ty : value; cap : value; sys : comp_sys} -> con
  | FCom : {dir : star; cap : value; sys : comp_sys} -> con
  | Box : {dir : star; cap : value; sys : box_sys} -> con

  | Univ : {kind : Kind.t; lvl : Lvl.t} -> con
  | V : {x : gen; ty0 : value; ty1 : value; equiv : value} -> con
  | VIn : {x : gen; el0 : value; el1 : value} -> con

  | Lam : clo -> con
  | ExtLam : abs -> con
  | CoRThunk : val_face -> con

  | Cons : value * value -> con
  | Bool : con
  | Tt : con
  | Ff : con

  | Up : {ty : value; neu : neu; sys : rigid_val_sys} -> con

  | LblTy : {lbl : string; args : nf list; ty : value} -> con
  | LblRet : value -> con

and neu =
  | Lvl : string option * int -> neu
  | Ref : Name.t * Tm.twin -> neu
  | Meta : Name.t -> neu
  | FunApp : neu * nf -> neu
  | ExtApp : neu * dim list -> neu
  | Car : neu -> neu
  | Cdr : neu -> neu

  | If : {mot : clo; neu : neu; tcase : value; fcase : value} -> neu

  (* Invariant: neu \in vty, vty is a V type *)
  | VProj : {x : gen; ty0 : value; ty1 : value; equiv : value; neu : neu} -> neu

  | Cap : {dir : star; ty : value; sys : comp_sys; neu : neu} -> neu

  | LblCall : neu -> neu
  | CoRForce : neu -> neu

and nf = {ty : value; el : value}

and ('x, 'a) face = ('x, 'a) Face.face

and clo =
  | Clo of {bnd : Tm.tm Tm.bnd; rho : env; rel : rel; action : D.action}

and env_el = Val of value | Atom of atom
and env = env_el list

and abs = value Abstraction.abs
and ext_abs = (value * val_sys) Abstraction.abs
and rigid_abs_face = ([`Rigid], abs) face
and val_face = ([`Any], value) face
and rigid_val_face = ([`Rigid], value) face

and comp_sys = rigid_abs_face list
and val_sys = val_face list
and rigid_val_sys = rigid_val_face list
and box_sys = rigid_val_sys

and node = Node of {con : con; action : D.action}
and value = node ref

let clo_name (Clo {bnd = Tm.B (nm, _); _}) =
  nm


module type S =
sig
  val make : con -> value
  val unleash : value -> con

  val reflect : value -> neu -> val_sys -> value

  val eval : rel -> env -> Tm.tm -> value
  val eval_cmd : rel -> env -> Tm.tm Tm.cmd -> value
  val eval_head : rel -> env -> Tm.tm Tm.head -> value
  val eval_frame : rel -> env -> value -> Tm.tm Tm.frame -> value
  val eval_dim : rel -> env -> Tm.tm -> Dim.repr
  val eval_tm_sys : rel -> env -> (Tm.tm, Tm.tm) Tm.system -> val_sys

  val apply : value -> value -> value
  val ext_apply : value -> dim list -> value
  val car : value -> value
  val cdr : value -> value
  val lbl_call : value -> value
  val corestriction_force : value -> value

  val inst_clo : clo -> value -> value

  val unleash_pi : ?debug:string list -> value -> value * clo
  val unleash_sg : ?debug:string list -> value -> value * clo
  val unleash_v : value -> gen * value * value * value
  val unleash_ext : value -> dim list -> value * val_sys
  val unleash_lbl_ty : value -> string * nf list * value
  val unleash_corestriction_ty : value -> val_face

  val pp_value : Format.formatter -> value -> unit
  val pp_neu : Format.formatter -> neu -> unit


  module Val : Sort.S
    with type t = value
    with type 'a m = 'a


  module ExtAbs : Abstraction.S
    with type el = value * val_sys

  module Abs : Abstraction.S
    with type el = value

  module Macro : sig
    val equiv : value -> value -> value
  end


  val base_restriction : Restriction.t
end

module type Sig =
sig
  val restriction : Restriction.t
  val lookup : Name.t -> Tm.twin -> Tm.tm * (Tm.tm, Tm.tm) Tm.system
end

module M (Sig : Sig) : S =
struct

  let base_restriction = Sig.restriction

  type step =
    | Ret : neu -> step
    | Step : value -> step

  let ret v = Ret v
  let step v = Step v

  module type Sort = Sort.S

  module Val : Sort with type t = value with type 'a m = 'a =
  struct

    type 'a m = 'a
    type t = value

    let act : D.action -> value -> value =
      fun phi thunk ->
        let Node node = !thunk in
        ref @@ Node {node with action = D.cmp phi node.action}
  end


  module Abs = Abstraction.M (Val)

  module ValFace = Face.M (Val)
  module AbsFace = Face.M (Abs)

  module Clo : Sort with type t = clo with type 'a m = 'a =
  struct
    type t = clo
    type 'a m = 'a

    let act phi clo =
      match clo with
      | Clo info ->
        Clo {info with action = D.cmp phi info.action}
  end

  module CompSys :
  sig
    include Sort
      with type t = comp_sys
      with type 'a m = [`Ok of comp_sys | `Proj of abs]
    val forall : D.atom -> t -> t
    val forallm : D.atom -> t m -> t m
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
        | Face.False p ->
          Face.False p :: act_aux phi sys
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
        | Face.False p ->
          Face.False p :: act_aux phi sys
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
    val forall : D.atom -> t -> t
  end =
  struct
    type t = val_sys
    type 'a m = 'a

    let act phi =
      List.map (ValFace.act phi)

    let from_rigid sys =
      let face : rigid_val_face -> val_face =
        function
        | Face.False p -> Face.False p
        | Face.Indet (p, a) -> Face.Indet (p, a)
      in
      List.map face sys

    (* note that these functions do not commute with `make`
     * if there is a face with equation `x=x` where `x` is
     * the dimension. *)
    let forall x sys =
      List.filter (fun f -> Face.forall x f = `Keep) sys
  end


  module ExtAbs : Abstraction.S with type el = value * val_sys =
    Abstraction.M (Sort.Prod (Val) (ValSys))

  exception ProjAbs of abs
  exception ProjVal of value


  let rec eval_dim rel rho tm =
    match Tm.unleash tm with
    | Tm.Dim0 ->
      D.Dim0
    | Tm.Dim1 ->
      D.Dim1
    | Tm.Up (hd, Emp) ->
      begin
        match hd with
        | Tm.Ix (i, _) ->
          begin
            match List.nth rho i with
            | Atom x ->
              R.canonize (D.Atom x) rel
            | _ ->
              failwith "eval_dim: expected atom in environment"
          end
        | Tm.Ref (a, _) ->
          R.canonize (D.Atom a) rel
        | Tm.Meta a ->
          R.canonize (D.Atom a) rel
        | _ -> failwith "eval_dim"
      end
    | _ -> failwith "eval_dim"

  let eval_dim_class rel rho tm =
    R.unleash (eval_dim rel rho tm) rel


  let rec make : con -> value =
    fun con ->
      match con with
      | Up up ->
        begin
          match unleash up.ty with
          | Rst rst ->
            begin
              match force_val_sys rst.sys with
              | `Proj el -> el
              | `Rigid sys ->
                make @@ Up {ty = rst.ty; neu = up.neu; sys}
            end
          | _ ->
            ref @@ Node {con; action = D.idn}
        end
      | _ ->
        ref @@ Node {con; action = D.idn}

  and act_can phi con =
    match con with
    | Pi info ->
      let dom = Val.act phi info.dom in
      let cod = Clo.act phi info.cod in
      make @@ Pi {dom; cod}

    | Sg info ->
      let dom = Val.act phi info.dom in
      let cod = Clo.act phi info.cod in
      make @@ Sg {dom; cod}

    | Ext abs ->
      let abs' = ExtAbs.act phi abs in
      make @@ Ext abs'

    | Rst info ->
      let ty = Val.act phi info.ty in
      let sys = ValSys.act phi info.sys in
      make @@ Rst {ty; sys}

    | CoR face ->
      let face = ValFace.act phi face in
      make @@ CoR face

    | Coe info ->
      make_coe
        (Star.act phi info.dir)
        (Abs.act phi info.abs)
        (Val.act phi info.el)

    | HCom info ->
      make_hcom
        (Star.act phi info.dir)
        (Val.act phi info.ty)
        (Val.act phi info.cap)
        (CompSys.act phi info.sys)

    | GHCom info ->
      make_ghcom
        (Star.act phi info.dir)
        (Val.act phi info.ty)
        (Val.act phi info.cap)
        (CompSys.act phi info.sys)

    | FCom info ->
      make_fcom
        (Star.act phi info.dir)
        (Val.act phi info.cap)
        (CompSys.act phi info.sys)

    | Box info ->
      make_box
        (Star.act phi info.dir)
        (Val.act phi info.cap)
        (BoxSys.act phi info.sys)

    | V info ->
      make_v
        (Gen.act phi info.x)
        (Val.act phi info.ty0)
        (Val.act phi info.ty1)
        (Val.act phi info.equiv)

    | VIn info ->
      make_vin
        (Gen.act phi info.x)
        (Val.act phi info.el0)
        (Val.act phi info.el1)

    | Univ _ ->
      make con

    | Bool ->
      make con

    | Tt ->
      make con

    | Ff ->
      make con

    | Lam clo ->
      make @@ Lam (Clo.act phi clo)

    | ExtLam abs ->
      make @@ ExtLam (Abs.act phi abs)

    | CoRThunk v ->
      make @@ CoRThunk (ValFace.act phi v)

    | Cons (v0, v1) ->
      make @@ Cons (Val.act phi v0, Val.act phi v1)

    | LblTy {lbl; ty; args} ->
      make @@ LblTy {lbl; ty = Val.act phi ty; args = List.map (act_nf phi) args}

    | LblRet v ->
      make @@ LblRet (Val.act phi v)

    | Up info ->
      let ty = Val.act phi info.ty in
      let sys = ValSys.act phi @@ ValSys.from_rigid info.sys in
      begin
        match force_val_sys sys with
        | `Proj v -> v
        | `Rigid sys ->
          match act_neu phi info.neu with
          | Ret neu ->
            make @@ Up {ty; neu; sys}
          | Step v ->
            v
      end

  and act_neu phi con =
    match con with
    | VProj info ->
      let mx = Gen.act phi info.x in
      let ty0 = Val.act phi info.ty0 in
      let ty1 = Val.act phi info.ty1 in
      let equiv = Val.act phi info.equiv in
      begin
        match act_neu phi info.neu with
        | Ret neu ->
          let vty = make_v mx ty0 ty1 equiv in
          let el = make @@ Up {ty = vty; neu = neu; sys = []} in
          step @@ vproj mx ~ty0 ~ty1 ~equiv ~el
        | Step el ->
          step @@ vproj mx ~ty0 ~ty1 ~equiv ~el
      end

    | Cap info ->
      let mdir = Star.act phi info.dir in
      let msys = CompSys.act phi info.sys in
      begin
        match act_neu phi info.neu with
        | Ret neu ->
          (* this is dumb; should refactor this with `cap`. *)
          let el = make @@ Up {ty = info.ty; neu; sys = []} in
          step @@ make_cap mdir info.ty msys el
        | Step el ->
          step @@ make_cap mdir info.ty msys el
      end

    | FunApp (neu, arg) ->
      let varg = act_nf phi arg in
      begin
        match act_neu phi neu with
        | Ret neu ->
          ret @@ FunApp (neu, varg)
        | Step v ->
          let {el; _} = varg in
          step @@ apply v el
      end

    | ExtApp (neu, rs) ->
      let rs = List.map (Dim.act phi) rs in
      begin
        match act_neu phi neu with
        | Ret neu ->
          ret @@ ExtApp (neu, rs)
        | Step v ->
          step @@ ext_apply v rs
      end

    | Car neu ->
      begin
        match act_neu phi neu with
        | Ret neu ->
          ret @@ Car neu
        | Step v ->
          step @@ car v
      end

    | Cdr neu ->
      begin
        match act_neu phi neu with
        | Ret neu ->
          ret @@ Cdr neu
        | Step v ->
          step @@ cdr v
      end

    | If info ->
      let mot = Clo.act phi info.mot in
      let tcase = Val.act phi info.tcase in
      let fcase = Val.act phi info.fcase in
      begin
        match act_neu phi info.neu with
        | Ret neu ->
          ret @@ If {mot; neu; tcase; fcase}
        | Step v ->
          step @@ if_ mot v tcase fcase
      end

    | LblCall neu ->
      begin
        match act_neu phi neu with
        | Ret neu ->
          ret @@ LblCall neu
        | Step v ->
          step @@ lbl_call v
      end

    | CoRForce neu ->
      begin
        match act_neu phi neu with
        | Ret neu ->
          ret @@ CoRForce neu
        | Step v ->
          step @@ corestriction_force v
      end

    | Lvl _ ->
      ret con

    | Ref _ ->
      ret con

    | Meta _ ->
      ret con

  and act_nf phi (nf : nf) =
    match nf with
    | info ->
      let ty = Val.act phi info.ty in
      let el = Val.act phi info.el in
      {ty; el}

  and force_abs_face face =
    match face with
    | Face.True (_, _, abs) ->
      raise @@ ProjAbs abs
    | Face.False xi ->
      Face.False xi
    | Face.Indet (xi, abs) ->
      Face.Indet (xi, abs)

  and force_val_face (face : val_face) =
    match face with
    | Face.True (_, _, v) ->
      raise @@ ProjVal v
    | Face.False xi ->
      Face.False xi
    | Face.Indet (xi, v) ->
      Face.Indet (xi, v)

  and force_val_sys sys =
    try
      `Rigid (List.map force_val_face sys)
    with
    | ProjVal v ->
      `Proj v

  and force_abs_sys sys =
    try
      `Ok (List.map force_abs_face sys)
    with
    | ProjAbs abs ->
      `Proj abs

  and unleash : value -> con =
    fun node ->
      let Node info = !node in
      match Dim.action_is_id info.action with
      | true ->
        info.con
      | false ->
        let node' = act_can info.action info.con in
        let con = unleash node' in
        node := Node {con = con; action = D.idn};
        con

  and make_cons (a, b) = make @@ Cons (a, b)

  and make_extlam abs = make @@ ExtLam abs

  and make_v mgen ty0 ty1 equiv : value =
    match mgen with
    | `Ok x ->
      make @@ V {x; ty0; ty1; equiv}
    | `Const `Dim0 ->
      ty0
    | `Const `Dim1 ->
      ty1

  and make_vin mgen el0 el1 : value =
    match mgen with
    | `Ok x ->
      rigid_vin x el0 el1
    | `Const `Dim0 ->
      el0
    | `Const `Dim1 ->
      el0

  and make_coe mdir abs el : value =
    match mdir with
    | `Ok dir ->
      rigid_coe dir abs el
    | `Same _ ->
      el

  and make_hcom mdir ty cap msys : value =
    match mdir with
    | `Ok dir ->
      begin
        match msys with
        | `Ok sys ->
          rigid_hcom dir ty cap sys
        | `Proj abs ->
          let _, r' = Star.unleash dir in
          Abs.inst1 abs r'
      end
    | `Same _ ->
      cap

  and make_ghcom mdir ty cap msys : value =
    match mdir with
    | `Ok dir ->
      begin
        match msys with
        | `Ok sys ->
          rigid_ghcom dir ty cap sys
        | `Proj abs ->
          let _, r' = Star.unleash dir in
          Abs.inst1 abs r'
      end
    | `Same _ ->
      cap

  and make_com mdir abs cap msys : value =
    match mdir with
    | `Ok dir ->
      let _, r' = Star.unleash dir in
      begin
        match msys with
        | `Ok sys ->
          rigid_com dir abs cap sys
        | `Proj abs ->
          Abs.inst1 abs r'
      end
    | `Same _ ->
      cap

  and make_gcom mdir abs cap msys : value =
    match mdir with
    | `Ok dir ->
      let _, r' = Star.unleash dir in
      begin
        match msys with
        | `Ok sys ->
          rigid_gcom dir abs cap sys
        | `Proj abs ->
          Abs.inst1 abs r'
      end
    | `Same _ ->
      cap

  and make_fcom mdir cap msys : value =
    match mdir with
    | `Ok dir ->
      begin
        match msys with
        | `Ok sys ->
          rigid_fcom dir cap sys
        | `Proj abs ->
          let _, r' = Star.unleash dir in
          Abs.inst1 abs r'
      end
    | `Same _ ->
      cap

  and make_box mdir cap msys : value =
    match mdir with
    | `Ok dir ->
      begin
        match msys with
        | `Ok sys ->
          rigid_box dir cap sys
        | `Proj el ->
          el
      end
    | `Same _ ->
      cap

  and rigid_vin x el0 el1 : value =
    make @@ VIn {x; el0; el1}

  and rigid_coe dir abs el =
    let x, tyx = Abs.unleash1 abs in
    match unleash tyx with
    | (Pi _ | Sg _ | Ext _ | Up _) ->
      make @@ Coe {dir; abs; el}

    | (Bool | Univ _) ->
      el

    | FCom info ->
      let r, r' = Star.unleash dir in
      let s, s' = Star.unleash info.dir in
      let cap_abs = Abs.bind1 x info.cap in

      (* this is different from the $O^z$ Part III becasue
       * `(D.subst r x)` applies to `z` as well. *)
      let origin z_dest =
        let face = Face.map @@
          fun ri r'i absi ->
          let y = Name.fresh () in
          Abs.bind1 y @@
          Val.act (D.equate ri r'i) @@
          make_coe (Star.make (D.named y) s) absi @@
          make_coe (Star.make s' (D.named y)) absi el
        in
        Val.act (D.subst r x) @@
        make_hcom
          (Star.make s' z_dest)
          info.cap
          (rigid_cap info.dir info.cap info.sys el)
          (`Ok (List.map face info.sys))
      in
      (* as in `origin`, substition applies to z_dest as well. this turns out to be okay. *)
      let recovery_apart abs x_dest z_dest =
        Val.act (D.subst x_dest x) @@
        make_coe (Star.make s' z_dest) abs @@
        make_coe (Star.make r x_dest) (Abs.bind1 x @@ Abs.inst1 abs s') el
      in
      let naively_coerced_cap =
        rigid_gcom dir cap_abs (origin s) @@
        CompSys.forall x @@
        let diag = AbsFace.rigid info.dir @@ Abs.bind1 x @@ make_coe (Star.make r (D.named x)) cap_abs el in
        let face = Face.map @@ fun ri r'i absi ->
          Abs.bind1 x @@
          Val.act (D.equate ri r'i) @@
          recovery_apart absi (D.named x) s
        in
        CompSys.forall x [diag] @ List.map face (CompSys.forall x info.sys)
      in
      let recovery_general abs z_dest =
        let phi_r' = D.subst r' x in
        make_gcom (Star.make (D.act phi_r' s) z_dest) (Abs.act phi_r' abs) naively_coerced_cap @@
        let diag = AbsFace.rigid dir @@
          let y = Name.fresh () in
          Abs.bind1 y @@ recovery_apart abs r (D.named y)
        in
        let face = Face.map @@ fun ri r'i absi ->
          let y = Name.fresh () in
          Abs.bind1 y @@ Val.act (D.equate ri r'i) @@ recovery_apart absi r' (D.named y)
        in
        `Ok (diag :: List.map face (CompSys.forall x info.sys))
      in
      let coerced_cap =
        (* this will be done in the final result: Val.act (D.subst r' x) @@ *)
        rigid_hcom info.dir info.cap naively_coerced_cap @@
        let diag = AbsFace.rigid dir @@ let w = Name.fresh () in Abs.bind1 w @@ origin (D.named w) in
        let face = Face.map @@ fun ri r'i absi ->
          let w = Name.fresh () in
          Abs.bind1 w @@
          Val.act (D.equate ri r'i) @@
          make_coe (Star.make (D.named w) s) absi @@
          recovery_general absi (D.named w)
        in
        diag :: List.map face info.sys
      in
      Val.act (D.subst r' x) @@
      rigid_box info.dir coerced_cap @@
      let face = Face.map @@ fun ri r'i absi ->
        Val.act (D.equate ri r'i) @@
        recovery_general absi s'
      in List.map face info.sys


    | V info ->
      begin
        let r, r' = Star.unleash dir in
        let abs0 = Abs.bind1 x info.ty0 in
        let abs1 = Abs.bind1 x info.ty1 in
        let subst0x = Val.act (D.subst D.dim0 x) in
        let ty00 = subst0x info.ty0 in
        let ty10 = subst0x info.ty1 in
        let equiv0 = subst0x info.equiv in

        match D.compare (Gen.unleash info.x) (D.named x) with
        | D.Same ->
          let base src dest =
            make_coe (Star.make src dest) abs1 @@
            let phi = D.subst src x in
            vproj (Gen.make src) (Val.act phi info.ty0) (Val.act phi info.ty1) (Val.act phi info.equiv) el
          in
          let base0 dest = base D.dim0 dest in
          let base1 dest = base D.dim1 dest in
          let fiber0 b = car @@ apply (cdr equiv0) b in
          let contr0 fib = apply (cdr @@ apply (cdr equiv0) (ext_apply (cdr fib) [D.dim1])) fib in
          let face_diag = AbsFace.make r r' @@ Abs.bind [Name.fresh ()] el in
          let face0 = AbsFace.make r D.dim0 @@ Abs.bind [Name.fresh ()] (base0 r') in
          let face1 = AbsFace.make r D.dim1 @@
            let y = Name.fresh () in
            Abs.bind1 y @@
            let ty = Val.act (D.subst r' x) info.ty1 in
            let cap = base1 r' in
            let msys = force_abs_sys @@
              let face0 = AbsFace.make r' D.dim0 @@
                let z = Name.fresh () in
                Abs.bind1 z @@ ext_apply (cdr (fiber0 cap)) [D.named z]
              in
              let face1 = AbsFace.make r' D.dim1 @@ Abs.bind [Name.fresh ()] el in
              [face0; face1]
            in
            make_hcom (Star.make D.dim1 (D.named y)) ty cap msys
          in
          let fiber0_ty b =
            let var i = Tm.up @@ Tm.var i `Only in
            eval (R.emp ()) [Val ty00; Val ty10; Val (car equiv0); Val b] @@
            Tm.Macro.fiber (var 0) (var 1) (var 2) (var 3)
          in
          let fixer_fiber =
            let fiber_at_face0 = make_cons (el, make_extlam @@ Abs.bind [Name.fresh ()] (base0 D.dim0)) in
            let mode = `SPLIT_COERCION in (* how should we switch this? *)
            match mode with
            | `SPLIT_COERCION ->
              begin
                match Gen.make r with
                | `Const `Dim0 -> fiber_at_face0
                | `Const `Dim1 -> fiber0 (base1 D.dim0)
                | `Ok r_gen ->
                  let r_atom = Gen.atom r_gen in
                  contr0 @@
                  make_coe (Star.make D.dim0 r) (Abs.bind1 r_atom (fiber0_ty (base r D.dim0))) @@
                  make_cons (Val.act (D.subst D.dim0 r_atom) el, make_extlam @@ Abs.bind [Name.fresh ()] (base0 D.dim0))
              end
            | `UNIFORM_HCOM ->
              make_hcom (Star.make D.dim1 D.dim0) (fiber0_ty (base r D.dim0)) (fiber0 (base r D.dim0)) @@
              force_abs_sys @@
              let face0 = AbsFace.make r D.dim0 @@
                let w = Name.fresh () in
                Abs.bind1 w @@
                ext_apply (contr0 fiber_at_face0) [D.named w]
              in
              let face1 = AbsFace.make r D.dim1 @@
                Abs.bind [Name.fresh ()] (fiber0 (base1 D.dim0))
              in
              [face0; face1]
            | `UNICORN ->
              failwith "too immortal; not suitable for mortal beings"
          in
          let el0 = car fixer_fiber in
          let face_front =
            AbsFace.make r' D.dim0 @@
            let w = Name.fresh () in
            Abs.bind1 w @@
            ext_apply (cdr fixer_fiber) [D.named w]
          in
          let el1 = make_hcom (Star.make D.dim1 D.dim0) info.ty1 (base r r') @@
            force_abs_sys [face0; face1; face_diag; face_front]
          in
          make_vin (Gen.make r') el0 el1

        | D.Apart ->
          let el0 = rigid_coe dir abs0 el in
          let el1 =
            let cap =
              let phi = Dim.subst r x in
              let ty0r = Val.act phi info.ty0 in
              let ty1r = Val.act phi info.ty1 in
              let equivr = Val.act phi info.equiv in
              rigid_vproj info.x ~el ~ty0:ty0r ~ty1:ty1r ~equiv:equivr
            in
            let r2x = Star.make r (D.named x) in
            let sys =
              let face0 =
                AbsFace.gen_const info.x `Dim0 @@
                Abs.bind1 x @@ apply (car info.equiv) @@
                make_coe r2x abs0 el
              in
              let face1 =
                AbsFace.gen_const info.x `Dim1 @@
                Abs.bind1 x @@
                make_coe r2x abs1 el
              in
              [face0; face1]
            in
            rigid_com dir abs1 cap sys
          in
          rigid_vin info.x el0 el1

        | D.Indeterminate ->
          failwith "impossible"
      end

    | _ ->
      failwith "TODO: rigid_coe"

  and rigid_hcom dir ty cap sys : value =
    match unleash ty with
    | (Pi _ | Sg _ | Ext _ | Up _) ->
      make @@ HCom {dir; ty; cap; sys}

    | Bool ->
      cap

    | Univ _ ->
      rigid_fcom dir cap sys

    | FCom info ->
      begin
        (* adapted from RedPRL *)

        let _, r' = Star.unleash dir in
        let s, s' = Star.unleash info.dir in
        let cap_in_wall = rigid_coe (Star.swap info.dir) in
        let hcom_of_coe abs =
          let face = Face.map @@ fun ri r'i absi ->
            let yi, eli = Abs.unleash1 absi in
            Abs.bind1 yi @@ Val.act (D.equate ri r'i) @@
            cap_in_wall abs eli in
          let y = Name.fresh () in
          Abs.bind1 y @@
          make_hcom
            (Star.make s (D.named y))
            info.cap
            (cap_in_wall abs cap)
            (`Ok (List.map face sys)) in

        let cap_of_hcom_in_wall abs dest =
          cap_in_wall abs @@
          make_hcom
            (Star.make s dest)
            (Abs.inst1 abs s')
            cap (`Ok sys) in

        let recovery abs recover_dim =
          let face0 = AbsFace.make recover_dim s @@ hcom_of_coe abs in
          let face1 = AbsFace.make recover_dim s' @@
            let y = Name.fresh () in
            Abs.bind1 y @@
            cap_of_hcom_in_wall abs (D.named y)
          in
          let face = Face.map @@ fun ri r'i absi ->
            let x, el = Abs.unleash1 absi in
            Abs.bind1 x @@
            Val.act (D.equate ri r'i) @@
            cap_in_wall abs el
          in
          match force_abs_sys [face0; face1] with
          | `Proj abs -> Abs.inst1 abs r'
          | `Ok faces ->
            rigid_hcom dir info.cap (cap_in_wall abs cap) @@ (faces @ List.map face sys)
        in

        let cap_aux el = rigid_cap info.dir info.cap info.sys el in

        let recovered =
          let diag_face = AbsFace.rigid dir @@
            let y = Name.fresh () in
            Abs.bind1 y @@ cap_aux cap
          in
          let hcom_faces =
            let face = Face.map @@
              fun _ _ absi ->
              let y = Name.fresh () in
              let z, el = Abs.unleash1 absi in
              Abs.bind1 y @@ Val.act (D.subst r' z) el
            in
            List.map face sys
          in
          let fcom_faces =
            let face = Face.map @@
              fun ri r'i absi ->
              let y = Name.fresh () in
              Abs.bind1 y @@ Val.act (D.equate ri r'i) @@
              recovery absi (D.named y)
            in
            List.map face info.sys
          in
          let inner_face = Face.map @@ fun ri r'i absi ->
            let y, el = Abs.unleash1 absi in
            Abs.bind1 y @@ Val.act (D.equate ri r'i) @@
            cap_aux el
          in
          rigid_hcom info.dir info.cap
            (rigid_hcom dir info.cap (cap_aux cap)
               (List.map inner_face sys))
            (diag_face :: hcom_faces @ fcom_faces)
        in
        let boundary = Face.map @@
          fun ri r'i absi ->
          Val.act (D.equate ri r'i) @@
          cap_of_hcom_in_wall absi s'
        in
        rigid_box info.dir recovered
          (List.map boundary sys)
      end

    | V {x; ty0; ty1; equiv} ->
      let r, _ = Star.unleash dir in
      let phi0 = D.equate (Gen.unleash x) D.dim0 in
      let el0 = Val.act phi0 @@ make_hcom (`Ok dir) ty0 cap (`Ok sys) in
      let el1 =
        let hcom r' ty = make_hcom (Star.make r r') ty cap (`Ok sys) in
        let face0 =
          AbsFace.gen_const x `Dim0 @@
          let y = Name.fresh () in
          Abs.bind1 y @@
          apply (car equiv) @@
          hcom (D.named y) ty0
        in
        let face1 =
          AbsFace.gen_const x `Dim1 @@
          let y = Name.fresh () in
          Abs.bind1 y @@
          hcom (D.named y) ty1
        in
        let el1_cap = rigid_vproj x ~ty0 ~ty1 ~equiv ~el:cap in
        let el1_sys =
          let face =
            Face.map @@ fun ri r'i absi ->
            let phi = D.equate ri r'i in
            let yi, el = Abs.unleash absi in
            Abs.bind yi @@ Val.act phi @@ rigid_vproj x ~ty0 ~ty1 ~equiv ~el
          in
          [face0; face1] @ List.map face sys
        in
        rigid_hcom dir ty1 el1_cap el1_sys
      in
      rigid_vin x el0 el1

    | _ ->
      failwith "TODO: rigid_hcom"

  and rigid_ghcom dir ty cap sys : value =
    match unleash ty with
    (* Who knows whether we can delay the expansion
     * in `Up _`? Please move `Up _` to the second
     * list if this does not work out. *)
    | (Pi _ | Sg _ | Up _) ->
      let rec drop_false sys =
        match sys with
        (* This is assuming false equations are made
         * of constants. Needs to revisit this when
         * we consider more cofibrations. *)
        | Face.False _ :: sys -> drop_false sys
        | _ -> sys
      in
      make @@ GHCom {dir; ty; cap; sys = drop_false sys}

    (* `Ext _`: the expansion will stop after a valid
     * correction system, so it is not so bad. *)
    | (Ext _ | Bool | Univ _ | FCom _ | V _) ->
      let rec aux sys =
        match sys with
        | [] -> cap
        | Face.False _ :: sys -> aux sys
        | Face.Indet (eqi, absi) :: rest ->
          let ri, r'i = Star.unleash eqi in
          let r, r' = Star.unleash dir in
          let face (dim0, dim1) =
            AbsFace.make ri D.dim0 @@
            (* XXX this would stop the expansion early, but is
             * unfortunately duplicate under `AbsFace.make` *)
            match CompSys.act (D.equate ri D.dim0) rest with
            | `Proj abs -> abs
            | `Ok rest0 ->
              let r'i = Dim.act (D.equate ri D.dim0) r'i in
              let ghcom00 = AbsFace.make r'i dim0 absi in
              let ghcom01 = AbsFace.make r'i dim1 @@
                let y = Name.fresh () in
                Abs.bind1 y @@
                (* TODO this can be optimized further by expanding
                 * `make_ghcom` because `ty` is not changed and
                 * in degenerate cases there is redundant renaming. *)
                make_ghcom (Star.make r (D.named y)) ty cap @@
                (* XXX this would stop the expansion early, but is
                 * unfortunately duplicate under `AbsFace.make` *)
                CompSys.act (D.equate r'i dim1) rest0
              in
              match force_abs_sys [ghcom00; ghcom01] with
              | `Proj abs -> abs
              | `Ok faces ->
                let y = Name.fresh () in
                Abs.bind1 y @@
                make_hcom (Star.make r (D.named y)) ty cap (`Ok (faces @ rest))
          in
          let face0 = face (D.dim0, D.dim1) in
          let face1 = face (D.dim1, D.dim0) in
          match force_abs_sys [face0; face1] with
          | `Proj abs -> Abs.inst1 abs r'
          | `Ok faces -> rigid_hcom dir ty cap (faces @ sys)
      in
      aux sys

    | _ ->
      failwith "TODO: rigid_ghcom"

  and rigid_com dir abs cap (sys : comp_sys) : value =
    let _, r' = Star.unleash dir in
    let ty = Abs.inst1 abs r' in
    let capcoe = rigid_coe dir abs cap in
    let syscoe : comp_sys =
      let face =
        Face.map @@ fun ri r'i absi ->
        let phi = D.equate ri r'i in
        let yi, vi = Abs.unleash1 absi in
        let y2r' = Star.make (D.named yi) (D.act phi r') in
        Abs.bind1 yi @@ make_coe y2r' (Abs.act phi abs) @@ Val.act phi vi
      in
      List.map face sys
    in
    rigid_hcom dir ty capcoe syscoe

  and rigid_gcom dir abs cap (sys : comp_sys) : value =
    let _, r' = Star.unleash dir in
    let ty = Abs.inst1 abs r' in
    let capcoe = rigid_coe dir abs cap in
    let syscoe : comp_sys =
      let face =
        Face.map @@ fun ri r'i absi ->
        let phi = D.equate ri r'i in
        let yi, vi = Abs.unleash1 absi in
        let y2r' = Star.make (D.named yi) (D.act phi r') in
        Abs.bind1 yi @@ make_coe y2r' (Abs.act phi abs) @@ Val.act phi vi
      in
      List.map face sys
    in
    rigid_ghcom dir ty capcoe syscoe

  and rigid_fcom dir cap sys : value =
    make @@ FCom {dir; cap; sys}

  and rigid_box dir cap sys : value =
    make @@ Box {dir; cap; sys}


  and clo bnd rel rho =
    Clo {bnd; rho; rel; action = D.idn}

  and eval rel rho tm =
    match Tm.unleash tm with
    | Tm.Pi (dom, cod) ->
      let dom = eval rel rho dom in
      let cod = clo cod rel rho in
      make @@ Pi {dom; cod}

    | Tm.Sg (dom, cod) ->
      let dom = eval rel rho dom in
      let cod = clo cod rel rho in
      make @@ Sg {dom; cod}

    | Tm.Ext bnd ->
      let abs = eval_ext_bnd rel rho bnd in
      make @@ Ext abs

    | Tm.Rst info ->
      let ty = eval rel rho info.ty in
      let sys = eval_tm_sys rel rho info.sys in
      make @@ Rst {ty; sys}

    | Tm.CoR tface ->
      let face = eval_tm_face rel rho tface in
      make @@ CoR face

    | Tm.V info ->
      let r = eval_dim_class rel rho info.r in
      let ty0 = eval rel rho info.ty0 in
      let ty1 = eval rel rho info.ty1 in
      let equiv = eval rel rho info.equiv in
      make_v (Gen.make r) ty0 ty1 equiv

    | Tm.Lam bnd ->
      make @@ Lam (clo bnd rel rho)

    | Tm.ExtLam bnd ->
      let abs = eval_nbnd rel rho bnd in
      make @@ ExtLam abs

    | Tm.CoRThunk face ->
      let vface = eval_tm_face rel rho face in
      make @@ CoRThunk vface

    | Tm.Cons (t0, t1) ->
      let v0 = eval rel rho t0 in
      let v1 = eval rel rho t1 in
      make @@ Cons (v0, v1)

    | Tm.FCom info ->
      let r = eval_dim_class rel rho info.r  in
      let r' = eval_dim_class rel rho info.r' in
      let dir = Star.make r r' in
      let cap = eval rel rho info.cap in
      let sys = eval_bnd_sys rel rho info.sys in
      make_fcom dir cap sys

    | Tm.Univ {kind; lvl} ->
      make @@ Univ {kind; lvl}

    | Tm.Bool ->
      make Bool

    | Tm.Tt ->
      make Tt

    | Tm.Ff ->
      make Ff

    | Tm.Dim0 ->
      failwith "0 is a dimension"

    | Tm.Dim1 ->
      failwith "1 is a dimension"

    | Tm.Up cmd ->
      eval_cmd rel rho cmd

    | Tm.Let (cmd, Tm.B (_, t)) ->
      let v0 = eval_cmd rel rho cmd in
      eval rel (Val v0 :: rho) t

    | Tm.LblTy info ->
      let ty = eval rel rho info.ty in
      let args = List.map (fun (ty, tm) -> {ty = eval rel rho ty; el = eval rel rho tm}) info.args in
      make @@ LblTy {lbl = info.lbl; ty; args}

    | Tm.LblRet t ->
      make @@ LblRet (eval rel rho t)

  and eval_cmd rel rho (hd, sp) =
    let vhd = eval_head rel rho hd in
    eval_stack rel rho vhd @@ Bwd.to_list sp

  and eval_stack rel rho vhd =
    function
    | [] -> vhd
    | frm :: stk ->
      let vhd = eval_frame rel rho vhd frm in
      eval_stack rel rho vhd stk

  and eval_frame rel rho vhd =
    function
    | Tm.LblCall ->
      lbl_call vhd
    | Tm.CoRForce ->
      corestriction_force vhd
    | Tm.FunApp t ->
      let v = eval rel rho t in
      apply vhd v
    | Tm.ExtApp ts ->
      let rs = List.map (eval_dim_class rel rho) ts in
      ext_apply vhd rs
    | Tm.Car ->
      car vhd
    | Tm.Cdr ->
      cdr vhd
    | Tm.VProj info ->
      let r = eval_dim_class rel rho info.r in
      let ty0 = eval rel rho info.ty0 in
      let ty1 = eval rel rho info.ty1 in
      let equiv = eval rel rho info.equiv in
      vproj (Gen.make r) ~ty0 ~ty1 ~equiv ~el:vhd
    | Tm.If info ->
      let mot = clo info.mot rel rho in
      let tcase = eval rel rho info.tcase in
      let fcase = eval rel rho info.fcase in
      if_ mot vhd tcase fcase


  and eval_head rel rho =
    function
    | Tm.Down info ->
      eval rel rho info.tm

    | Tm.Coe info ->
      let r = eval_dim_class rel rho info.r in
      let r' = eval_dim_class rel rho info.r' in
      let dir = Star.make r r' in
      let abs = eval_bnd rel rho info.ty  in
      let el = eval rel rho info.tm in
      make_coe dir abs el

    | Tm.HCom info ->
      let r = eval_dim_class rel rho info.r in
      let r' = eval_dim_class rel rho info.r' in
      let dir = Star.make r r' in
      let ty = eval rel rho info.ty in
      let cap = eval rel rho info.cap in
      let sys = eval_bnd_sys rel rho info.sys in
      make_hcom dir ty cap sys

    | Tm.Com info ->
      let r = eval_dim_class rel rho info.r in
      let r' = eval_dim_class rel rho info.r' in
      let dir = Star.make r r' in
      let abs = eval_bnd rel rho info.ty in
      let cap = eval rel rho info.cap in
      let sys = eval_bnd_sys rel rho info.sys in
      make_com dir abs cap sys

    | Tm.Ix (i, _) ->
      begin
        match List.nth rho i with
        | Val v -> v
        | Atom a ->
          Format.eprintf "Expected value in environment for %i, but found atom %a@." i Name.pp a;
          failwith "Expected value in environment"
      end

    | Tm.Ref (name, tw) ->
      let tty, tsys = Sig.lookup name tw in
      let vsys = eval_tm_sys rel [] tsys in
      let vty = eval rel [] tty in
      reflect vty (Ref (name, tw)) vsys

    | Tm.Meta name ->
      let tty, tsys = Sig.lookup name `Only in
      let vsys = eval_tm_sys rel [] tsys in
      let vty = eval rel [] tty in
      reflect vty (Meta name) vsys

  and reflect ty neu sys =
    match force_val_sys sys with
    | `Proj el -> el
    | `Rigid sys ->
      make @@ Up {ty; neu; sys}

  and eval_bnd_face rel rho (tr, tr', obnd) =
    let r = eval_dim rel rho tr in
    let r' = eval_dim rel rho tr' in
    let sr = R.unleash r rel in
    let sr' = R.unleash r' rel in
    match Star.make sr sr' with
    | `Ok xi ->
      begin
        match D.compare sr sr' with
        | D.Apart ->
          Face.False xi
        | _ ->
          let bnd = Option.get_exn obnd in
          let rel' = R.equate r r' rel in
          let abs = eval_bnd rel' rho bnd in
          Face.Indet (xi, abs)
      end
    | `Same _ ->
      let bnd = Option.get_exn obnd in
      let abs = eval_bnd rel rho bnd in
      Face.True (sr, sr', abs)

  and eval_bnd_sys rel rho sys  =
    try
      let sys =
        List.map
          (fun x -> force_abs_face @@ eval_bnd_face rel rho x)
          sys
      in `Ok sys
    with
    | ProjAbs abs ->
      `Proj abs

  and eval_tm_face rel rho (tr, tr', otm) : val_face =
    let r = eval_dim rel rho tr in
    let r' = eval_dim rel rho tr' in
    let sr = R.unleash r rel in
    let sr' = R.unleash r' rel in
    match Star.make sr sr' with
    | `Ok xi ->
      begin
        match D.compare sr sr' with
        | D.Apart ->
          Face.False xi
        | _ ->
          let tm = Option.get_exn otm in
          let rel' = R.equate r r' rel in
          let el = eval rel' rho tm in
          Face.Indet (xi, el)
      end
    | `Same _ ->
      let tm = Option.get_exn otm in
      let el = eval rel rho tm in
      Face.True (sr, sr', el)

  and eval_tm_sys rel rho sys : val_sys =
    List.map (eval_tm_face rel rho) sys

  and eval_bnd rel rho bnd =
    let Tm.B (_, tm) = bnd in
    let x = Name.fresh () in
    let rho = Atom x :: rho in
    Abs.bind1 x @@ eval rel rho tm

  and eval_nbnd rel rho bnd =
    let Tm.NB (nms, tm) = bnd in
    let xs = List.map Name.named nms in
    let rho = List.map (fun x -> Atom x) xs @ rho in
    Abs.bind xs @@ eval rel rho tm

  and eval_ext_bnd rel rho bnd =
    let Tm.NB (nms, (tm, sys)) = bnd in
    let xs = List.map Name.named nms in
    let rho = List.map (fun x -> Atom x) xs @ rho in
    ExtAbs.bind xs (eval rel rho tm, eval_tm_sys rel rho sys)

  and unleash_pi ?debug:(debug = []) v =
    match unleash v with
    | Pi {dom; cod} -> dom, cod
    | Rst rst -> unleash_pi ~debug rst.ty
    | _ ->
      Format.eprintf "%a: tried to unleash %a as pi type@."
        pp_trace debug
        pp_value v;
      failwith "unleash_pi"

  and unleash_sg ?debug:(debug = []) v =
    match unleash v with
    | Sg {dom; cod} -> dom, cod
    | Rst rst -> unleash_sg rst.ty
    | _ ->
      Format.eprintf "%a: tried to unleash %a as sigma type@."
        pp_trace debug
        pp_value v;
      failwith "unleash_sg"

  and unleash_ext v rs =
    match unleash v with
    | Ext abs ->
      ExtAbs.inst abs rs
    | Rst rst ->
      unleash_ext rst.ty rs
    | _ ->
      Format.printf "unleash_ext: %a@." pp_value v;
      failwith "unleash_ext"

  and unleash_v v =
    match unleash v with
    | V {x; ty0; ty1; equiv} ->
      x, ty0, ty1, equiv
    | Rst rst ->
      unleash_v rst.ty
    | _ ->
      failwith "unleash_v"

  and unleash_lbl_ty v =
    match unleash v with
    | LblTy {lbl; args; ty} ->
      lbl, args, ty
    | Rst rst ->
      unleash_lbl_ty rst.ty
    | _ ->
      failwith "unleash_lbl_ty"

  and unleash_corestriction_ty v =
    match unleash v with
    | CoR face ->
      face
    | Rst rst ->
      unleash_corestriction_ty rst.ty
    | _ ->
      failwith "unleash_corestriction_ty"

  and pp_trace fmt trace =
    Format.fprintf fmt "@[[%a]@]"
      (Format.pp_print_list Format.pp_print_string)
      trace


  and lbl_call v =
    match unleash v with
    | LblRet v -> v
    | Up info ->
      let _, _, ty = unleash_lbl_ty info.ty in
      let call = LblCall info.neu in
      let call_face =
        Face.map @@ fun _ _ a ->
        lbl_call a
      in
      let call_sys = List.map call_face info.sys in
      make @@ Up {ty; neu = call; sys = call_sys}
    | _ ->
      failwith "lbl_call"

  and corestriction_force v =
    match unleash v with
    | CoRThunk face ->
      begin
        match face with
        | Face.True (_, _, v) -> v
        | _ -> failwith "Cannot force corestriction when it doesn't hold"
      end

    | Up info ->
      begin
        match unleash_corestriction_ty info.ty with
        | Face.True (_, _, ty) ->
          let force = CoRForce info.neu in
          let force_face =
            Face.map @@ fun _ _ a ->
            corestriction_force a
          in
          let force_sys = List.map force_face info.sys in
          make @@ Up {ty; neu = force; sys = force_sys}
        | _ ->
          failwith "Cannot force non-true corestriction"
      end
    | _ ->
      failwith "corestriction_force"

  and apply vfun varg =
    match unleash vfun with
    | Lam clo ->
      inst_clo clo varg

    | Up info ->
      let dom, cod = unleash_pi ~debug:["apply"; "up"] info.ty in
      let cod' = inst_clo cod varg in
      let app = FunApp (info.neu, {ty = dom; el = varg}) in
      let app_face =
        Face.map @@ fun r r' a ->
        apply a @@ Val.act (D.equate r r') varg
      in
      let app_sys = List.map app_face info.sys in
      make @@ Up {ty = cod'; neu = app; sys = app_sys}

    | Coe info ->
      let r, r' = Star.unleash info.dir in
      let x, tyx = Abs.unleash1 info.abs in
      let domx, codx = unleash_pi ~debug:["apply"; "coe"] tyx in
      let abs =
        Abs.bind1 x @@
        inst_clo codx @@
        make_coe
          (Star.make r' (D.named x))
          (Abs.bind1 x domx)
          varg
      in
      let el =
        apply info.el @@
        make_coe
          (Star.make r' r)
          (Abs.bind1 x domx)
          varg
      in
      rigid_coe info.dir abs el

    | HCom info ->
      let _, cod = unleash_pi ~debug:["apply"; "hcom"] info.ty in
      let ty = inst_clo cod varg in
      let cap = apply info.cap varg in
      let app_face =
        Face.map @@ fun r r' abs ->
        let x, v = Abs.unleash1 abs in
        Abs.bind1 x @@ apply v (Val.act (D.equate r r') varg)
      in
      let sys = List.map app_face info.sys in
      rigid_hcom info.dir ty cap sys

    | GHCom info ->
      let _, cod = unleash_pi ~debug:["apply"; "ghcom"] info.ty in
      let ty = inst_clo cod varg in
      let cap = apply info.cap varg in
      let app_face =
        Face.map @@ fun r r' abs ->
        let x, v = Abs.unleash1 abs in
        Abs.bind1 x @@ apply v (Val.act (D.equate r r') varg)
      in
      let sys = List.map app_face info.sys in
      rigid_ghcom info.dir ty cap sys

    | _ ->
      failwith "apply"

  and ext_apply vext ss =
    match unleash vext with
    | ExtLam abs ->
      Abs.inst abs ss

    | Up info ->
      let tyr, sysr = unleash_ext info.ty ss in
      begin
        match force_val_sys sysr with
        | `Rigid sysr ->
          let app = ExtApp (info.neu, ss) in
          let app_face =
            Face.map @@ fun r r' a ->
            ext_apply a @@ List.map (Dim.act (Dim.equate r r')) ss
          in
          let app_sys = List.map app_face info.sys in
          make @@ Up {ty = tyr; neu = app; sys = sysr @ app_sys}
        | `Proj v ->
          v
      end

    | Coe info ->
      let y, ext_y = Abs.unleash1 info.abs in
      let ty_s, sys_s = unleash_ext ext_y ss in
      let forall_y_sys_s = ValSys.forall y sys_s in
      begin
        match force_val_sys forall_y_sys_s with
        | `Proj v ->
          v

        | `Rigid rsys ->
          let correction =
            let face = Face.map @@ fun _ _ v -> Abs.bind1 y v in
            List.map face rsys
          in
          let abs = Abs.bind1 y ty_s in
          let cap = ext_apply info.el ss in
          rigid_com info.dir abs cap correction
      end

    | HCom info ->
      let ty_s, sys_s = unleash_ext info.ty ss in
      begin
        match force_val_sys sys_s with
        | `Proj v ->
          v
        | `Rigid boundary_sys ->
          let cap = ext_apply info.cap ss in
          let correction_sys =
            let face = Face.map @@ fun _ _ v -> Abs.bind [Name.fresh ()] v in
            List.map face boundary_sys
          in
          rigid_hcom info.dir ty_s cap @@ correction_sys @ info.sys
      end

    | _ ->
      failwith "ext_apply"


  and vproj mgen ~ty0 ~ty1 ~equiv ~el : value =
    match mgen with
    | `Ok x ->
      rigid_vproj x ~ty0 ~ty1 ~equiv ~el
    | `Const `Dim0 ->
      let func = car equiv in
      apply func el
    | `Const `Dim1 ->
      el

  and rigid_vproj x ~ty0 ~ty1 ~equiv ~el : value =
    match unleash el with
    | VIn info ->
      info.el1
    | Up up ->
      let neu = VProj {x; ty0; ty1; equiv; neu = up.neu} in
      let vproj_face =
        Face.map @@ fun r r' a ->
        let phi = Dim.equate r r' in
        vproj (Gen.act phi x) ~ty0:(Val.act phi ty0) ~ty1:(Val.act phi ty1) ~equiv:(Val.act phi equiv) ~el:a
      in
      let vproj_sys = List.map vproj_face up.sys in
      make @@ Up {ty = ty1; neu; sys = vproj_sys}
    | _ ->
      failwith "rigid_vproj"

  and if_ mot scrut tcase fcase =
    match unleash scrut with
    | Tt ->
      tcase
    | Ff ->
      fcase
    | Up up ->
      let neu = If {mot; neu = up.neu; tcase; fcase} in
      let mot' = inst_clo mot scrut in
      let if_face =
        Face.map @@ fun r r' a ->
        let phi = Dim.equate r r' in
        if_ (Clo.act phi mot) a (Val.act phi tcase) (Val.act phi fcase)
      in
      let if_sys = List.map if_face up.sys in
      make @@ Up {ty = mot'; neu; sys = if_sys}
    | _ ->
      failwith "if_"

  and car v =
    match unleash v with
    | Cons (v0, _) ->
      v0

    | Up info ->
      let dom, _ = unleash_sg ~debug:["Val.car"] info.ty in
      let car_sys = List.map (Face.map (fun _ _ a -> car a)) info.sys in
      make @@ Up {ty = dom; neu = Car info.neu; sys = car_sys}

    | Coe info ->
      let x, tyx = Abs.unleash1 info.abs in
      let domx, _ = unleash_sg tyx in
      let abs = Abs.bind1 x domx in
      let el = car info.el in
      rigid_coe info.dir abs el

    | HCom info ->
      let dom, _ = unleash_sg info.ty in
      let cap = car info.cap in
      let face =
        Face.map @@ fun _ _ abs ->
        let y, v = Abs.unleash1 abs in
        Abs.bind1 y @@ car v
      in
      let sys = List.map face info.sys in
      rigid_hcom info.dir dom cap sys

    | GHCom info ->
      let dom, _ = unleash_sg info.ty in
      let cap = car info.cap in
      let face =
        Face.map @@ fun _ _ abs ->
        let y, v = Abs.unleash1 abs in
        Abs.bind1 y @@ car v
      in
      let sys = List.map face info.sys in
      rigid_ghcom info.dir dom cap sys

    | _ ->
      failwith "car"

  and cdr v =
    match unleash v with
    | Cons (_, v1) ->
      v1

    | Up info ->
      let _, cod = unleash_sg info.ty in
      let cdr_sys = List.map (Face.map (fun _ _ a -> cdr a)) info.sys in
      let cod_car = inst_clo cod @@ car v in
      make @@ Up {ty = cod_car; neu = Cdr info.neu; sys = cdr_sys}

    | Coe info ->
      let abs =
        let x, tyx = Abs.unleash1 info.abs in
        let domx, codx = unleash_sg tyx in
        let r, _ = Star.unleash info.dir in
        let coerx =
          make_coe
            (Star.make r (D.named x))
            (Abs.bind1 x domx)
            (car info.el)
        in
        Abs.bind1 x @@ inst_clo codx coerx
      in
      let el = cdr info.el in
      rigid_coe info.dir abs el

    | HCom info ->
      let abs =
        let r, _ = Star.unleash info.dir in
        let dom, cod = unleash_sg info.ty in
        let z = Name.fresh () in
        let msys =
          let face =
            Face.map @@ fun _ _ absi ->
            let yi, vi = Abs.unleash absi in
            Abs.bind yi @@ car vi
          in
          `Ok (List.map face info.sys)
        in
        let hcom =
          make_hcom
            (Star.make r (D.named z))
            dom
            (car info.cap)
            msys
        in
        Abs.bind1 z @@ inst_clo cod hcom
      in
      let cap = cdr info.cap in
      let sys =
        let face =
          Face.map @@ fun _ _ absi ->
          let yi, vi = Abs.unleash absi in
          Abs.bind yi @@ cdr vi
        in
        List.map face info.sys
      in
      rigid_com info.dir abs cap sys

    | GHCom info ->
      let abs =
        let r, _ = Star.unleash info.dir in
        let dom, cod = unleash_sg info.ty in
        let z = Name.fresh () in
        let msys =
          let face =
            Face.map @@ fun _ _ absi ->
            let yi, vi = Abs.unleash absi in
            Abs.bind yi @@ car vi
          in
          `Ok (List.map face info.sys)
        in
        let hcom =
          make_ghcom
            (Star.make r (D.named z))
            dom
            (car info.cap)
            msys
        in
        Abs.bind1 z @@ inst_clo cod hcom
      in
      let cap = cdr info.cap in
      let sys =
        let face =
          Face.map @@ fun _ _ absi ->
          let yi, vi = Abs.unleash absi in
          Abs.bind yi @@ cdr vi
        in
        List.map face info.sys
      in
      rigid_gcom info.dir abs cap sys

    | _ -> failwith "TODO: cdr"

  and make_cap mdir ty msys el : value =
    match mdir with
    | `Ok dir ->
      begin
        match msys with
        | `Ok sys ->
          rigid_cap dir ty sys el
        | `Proj abs ->
          rigid_coe (Star.swap dir) abs el
      end
    | `Same _ ->
      el

  and rigid_cap dir ty sys el : value =
    match unleash el with
    | Box info -> info.cap
    | Up info ->
      let cap_sys = List.map (Face.map (fun _ _ a -> rigid_cap dir ty sys a)) info.sys in
      make @@ Up {ty; neu = Cap {dir; neu = info.neu; ty; sys}; sys = cap_sys}
    | _ -> failwith "rigid_cap"


  and inst_clo clo varg =
    match clo with
    | Clo info ->
      let Tm.B (_, tm) = info.bnd in
      Val.act info.action @@
      eval info.rel (Val varg :: info.rho) tm


  and pp_env_cell fmt =
    function
    | Val v -> pp_value fmt v
    | Atom a -> Name.pp fmt a

  and pp_env fmt =
    let pp_sep fmt () = Format.fprintf fmt ", " in
    Format.pp_print_list ~pp_sep pp_env_cell fmt

  and pp_value fmt value =
    match unleash value with
    | Up up ->
      Format.fprintf fmt "%a{%a}" pp_neu up.neu pp_val_sys up.sys
    | Lam clo ->
      Format.fprintf fmt "@[<1>(λ@ %a)@]" pp_clo clo
    | ExtLam abs ->
      Format.fprintf fmt "@[<1>(λ@ %a)@]" pp_abs abs
    | CoRThunk face ->
      Format.fprintf fmt "@[<1>{%a}@]" pp_val_face face
    | Tt ->
      Format.fprintf fmt "tt"
    | Ff ->
      Format.fprintf fmt "ff"
    | Bool ->
      Format.fprintf fmt "bool"
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
      Format.fprintf fmt "@[<1>(cons@ %a %a)@]" pp_value v0 pp_value v1
    | V _ ->
      Format.fprintf fmt "<v-type>"
    | VIn _ ->
      Format.fprintf fmt "<vin>"
    | Coe _ ->
      Format.fprintf fmt "<coe>"
    | HCom _ ->
      Format.fprintf fmt "<hcom>"
    | GHCom _ ->
      Format.fprintf fmt "<ghcom>"
    | FCom _ ->
      Format.fprintf fmt "<fcom>"
    | Box _ ->
      Format.fprintf fmt "<box>" (* 📦 *)
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

  and pp_abs fmt abs =
    let x, v = Abs.unleash1 abs in
    Format.fprintf fmt "@[<1><%a>@ %a@]" Name.pp x pp_value v

  and pp_ext_abs fmt abs =
    let x, (tyx, sysx) = ExtAbs.unleash1 abs in
    Format.fprintf fmt "@[<1><%a>@ %a@ %a@]" Name.pp x pp_value tyx pp_val_sys sysx

  and pp_val_sys : type x. Format.formatter -> (x, value) face list -> unit =
    fun fmt ->
      let pp_sep fmt () = Format.fprintf fmt " " in
      Format.pp_print_list ~pp_sep pp_val_face fmt

  and pp_val_face : type x. _ -> (x, value) face -> unit =
    fun fmt ->
      function
      | Face.True (r0, r1, v) ->
        Format.fprintf fmt "@[<1>[!%a=%a@ %a]@]" Dim.pp r0 Dim.pp r1 pp_value v
      | Face.False p ->
        let r0, r1 = Star.unleash p in
        Format.fprintf fmt "@[<1>[%a/=%a]@]" Dim.pp r0 Dim.pp r1
      | Face.Indet (p, v) ->
        let r0, r1 = Star.unleash p in
        Format.fprintf fmt "@[<1>[?%a=%a %a]@]" Dim.pp r0 Dim.pp r1 pp_value v

  and pp_clo fmt _ =
    Format.fprintf fmt "<clo>"

  and pp_neu fmt neu =
    match neu with
    | Lvl (None, i) ->
      Format.fprintf fmt "#%i" i

    | Lvl (Some x, _) ->
      Uuseg_string.pp_utf_8 fmt x

    | FunApp (neu, arg) ->
      Format.fprintf fmt "@[<1>(%a@ %a)@]" pp_neu neu pp_value arg.el

    | ExtApp (neu, args) ->
      Format.fprintf fmt "@[<1>(%s@ %a@ %a)@]" "@" pp_neu neu pp_dims args

    | Car neu ->
      Format.fprintf fmt "@[<1>(car %a)@]" pp_neu neu

    | Cdr neu ->
      Format.fprintf fmt "@[<1>(cdr %a)@]" pp_neu neu

    | Ref (a, _) ->
      Name.pp fmt a

    | Meta alpha ->
      Name.pp fmt alpha

    | If _ ->
      Format.fprintf fmt "<if>"

    | Cap _ ->
      Format.fprintf fmt "<cap>"

    | VProj _ ->
      Format.fprintf fmt "<vproj>"

    | LblCall neu ->
      Format.fprintf fmt "@[<1>(call %a)@]" pp_neu neu

    | CoRForce neu ->
      Format.fprintf fmt "@[<1>(! %a)@]" pp_neu neu


  and pp_nf fmt nf =
    pp_value fmt nf.el

  and pp_nfs fmt nfs =
    let pp_sep fmt () = Format.fprintf fmt " " in
    Format.pp_print_list ~pp_sep pp_nf fmt nfs

  and pp_dims fmt rs =
    let pp_sep fmt () = Format.fprintf fmt " " in
    Format.pp_print_list ~pp_sep Dim.pp fmt rs

  module Macro =
  struct
    let equiv ty0 ty1 : value =
      let rho = [Val ty0; Val ty1] in
      eval (R.emp ()) rho @@
      Tm.Macro.equiv
        (Tm.up @@ Tm.var 0 `Only)
        (Tm.up @@ Tm.var 1 `Only)

  end

end
