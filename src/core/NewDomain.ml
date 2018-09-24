open RedBasis
open Bwd
open BwdNotation

exception PleaseFillIn

type dim = I.t

(** The dimension equality oracle *)
module Rel = NewRestriction
type rel = Rel.t

(* this module provides the data type to hold an optional rel to
 * facilitate the dropping of `run phi1` in `run phi2 @@ run phi1 a`.
 *
 * the inner datatype is mutable in order to remember the result. *)
module Delay :
sig
  type 'a t
  val make : 'a -> 'a t
  val make' : rel option -> 'a -> 'a t

  (* this is a brutal API to get the raw data out. *)
  val drop_rel : 'a t -> 'a

  (* this is a convenience function to create a new delayed X.run
   * with a new rel. *)
  val with_rel : rel -> 'a t -> 'a t

  (* this is to force the result. the first argument is intended
   * to be X.run where X is some structure implementing Domain. *)
  val out : (rel -> 'a -> 'a) -> 'a t -> 'a

  (* this is to break down the inner structure *)
  val fold : (rel option -> 'a -> 'b) -> 'a t -> 'b
end =
struct
  type 'a delayed_record =
    {rel : rel option;
     data : 'a}

  type 'a t = 'a delayed_record ref

  let make' r d = ref {data = d; rel = r}

  let make d = make' None d

  let drop_rel v = !v.data

  let with_rel r v = make' (Some r) (drop_rel v)

  let out f v =
    match !v.rel with
    | Some r -> let d = f r !v.data in v := {data = d; rel = None}; d
    | None -> !v.data

  let fold f v = f !v.rel !v.data
end

type 'a face = dim * dim * 'a Lazy.t Delay.t
type 'a sys = 'a face list
type 'a abs = Abs of Name.t * 'a

(** This is the type of "prevalues", that is the domain from which values come.
    A prevalue can be judged to be a value with respect to a restriction / dimension
    theory. I think we will not write code that checks that something is a value, but instead
    make this involved in the pre-and-post- conditions of the semantic operations. *)
type con =
  | Pi of quantifier
  | Sg of quantifier
  | Ext of ext_clo

  | Lam of clo
  | ExtLam of nclo
  | Cons of value * value
  | Coe of {r : dim; r' : dim; ty : coe_shape; cap : value}
  | HCom of {r : dim; r' : dim; ty : hcom_shape; cap : value; sys : con abs sys}
  | Neu of {ty : value; neu : neu; sys : con sys}

and value = con Delay.t
and lazy_value = con Lazy.t Delay.t

and quantifier =
  {dom : value;
   cod : clo}

and coe_shape =
  [ `Pi of quantifier abs   (** coe in pi *)
  | `Sg of quantifier abs   (** coe in sigma *)
  | `Ext of ext_clo abs     (** coe in extension type *)
  ]

and hcom_shape =
  [ `Pi of quantifier   (** hcom in pi *)
  | `Sg of quantifier   (** hcom in sigma *)
  | `Ext of ext_clo     (** hcom in extension type *)
  | `Pos                (** fhcom, i.e. hcom in positive types *)
  ]


and head =
  | Lvl of int
  | NCoe of {r : dim; r' : dim; ty : neu abs; cap : value}

and frame =
  | FunApp of value
  | ExtApp of dim list
  | Car
  | Cdr
  | NHCom of {r : dim; r' : dim; cap : value; sys : con abs sys}

and neu =
  {head : head;
   frames : frame bwd}

and cell =
  | Val of lazy_value
  | Dim of dim

and env = cell bwd

and clo = Clo of {bnd : Tm.tm Tm.bnd; env : env}
and nclo = NClo of {bnd : Tm.tm Tm.nbnd; env : env}
and ext_clo = ExtClo of {bnd : (Tm.tm * (Tm.tm, Tm.tm) Tm.system) Tm.nbnd; env : env}


let flip f x y = f y x

(** Permutations *)
module Perm :
sig
  type t
  val freshen_name : Name.t -> Name.t * t
  val freshen_names : Name.t bwd -> Name.t bwd * t
  val swap_name : t -> Name.t -> Name.t
end =
struct
  type t = (Name.t * Name.t) list (* favonia: a demonstration of my laziness *)
  let mimic x = Name.named (Name.name x)
  let freshen_name x =
    let x' = mimic x in x', [(x, x')]
  let rec freshen_names = function
    | Emp -> Emp, []
    | Snoc (xs, x) ->
      let xs', perm = freshen_names xs in
      let x' = mimic x in
      Snoc (xs', x'), (x, x') :: perm
  let swap_name perm x =
    try List.assoc x perm with Not_found -> x
end

type perm = Perm.t

module type Domain =
sig
  type t

  (** [swap] is a purely syntactic operation which perserves the property of being a Ξ-value. *)
  val swap : perm -> t -> t

  (** [subst] is a purely syntactic operation that does {e not} preserve the property of being a Ξ-value; it should usually be followed by [run] with extended Ξ. *)
  val subst : dim -> Name.t -> t -> t

  (** [run] brings the element underneath the restriction Ξ. *)
  val run : rel -> t -> t

  (** [subst_then_run] is semantically [subst] followed by [run], but may be more optimized *)
  val subst_then_run : rel -> dim -> Name.t -> t -> t
end

module type DomainPlug =
sig
  include Domain

  (** Plug applies a stack frame to an element of the domain. *)
  val plug : rel -> frame -> t -> t
end

module type DelayedDomainPlug =
functor (X : DomainPlug) ->
sig
  include DomainPlug with type t = X.t Delay.t

  (* undo Delay.make *)
  val out : t -> X.t

  (* convenience functions that are hopefully self-explanatory *)
  val hsubst : dim -> Name.t -> rel -> t -> t
  val subst_then_run_then_out : rel -> dim -> Name.t -> t -> X.t
  val run_then_out : rel -> t -> X.t
end

module rec Syn :
sig
  type t = Tm.tm
  val eval : rel -> env -> t -> con
  val eval_tm_sys : rel -> env -> (t, t) Tm.system -> con sys
end =
struct
  type t = Tm.tm
  let eval _ _ =
    raise PleaseFillIn

  let eval_tm_sys _ _ = raise PleaseFillIn
end

and Dim : Domain with type t = dim =
struct
  type t = dim
  let swap pi =
    function
    | `Dim0 | `Dim1 as r -> r
    | `Atom x -> `Atom (Perm.swap_name pi x)

  let subst r x =
    function
    | `Dim0 | `Dim1 as r -> r
    | `Atom y when x = y -> r
    | r -> r

  let run _ r = r

  let subst_then_run _ r x =
    subst r x
end

and Clo :
sig
  include Domain with type t = clo
  val inst : rel -> t -> cell -> con
end =
struct
  type t = clo

  let swap _ _ = raise PleaseFillIn
  let subst _ _ = raise PleaseFillIn
  let run _ _ = raise PleaseFillIn
  let subst_then_run _ _ _ _ = raise PleaseFillIn

  let inst rel clo cell =
    let Clo {bnd; env} = clo in
    let Tm.B (_, tm) = bnd in
    Syn.eval rel (env #< cell) tm
end

and NClo :
sig
  include Domain with type t = nclo
  val inst : rel -> t -> cell list -> con
end =
struct
  type t = nclo

  let swap _ _ = raise PleaseFillIn
  let subst _ _ = raise PleaseFillIn
  let run _ _ = raise PleaseFillIn
  let subst_then_run _ _ _ _ = raise PleaseFillIn

  let inst (rel : rel) nclo cells : con =
    let NClo {bnd; env} = nclo in
    let Tm.NB (_, tm) = bnd in
    Syn.eval rel (env <>< cells) tm
end

and ExtClo :
sig
  include Domain with type t = ext_clo
  val inst : rel -> t -> cell list -> con * con sys
  val inst' : rel -> t -> cell list -> value * con sys
end =
struct
  type t = ext_clo

  let swap _ _ = raise PleaseFillIn
  let subst _ _ = raise PleaseFillIn
  let run _ _ = raise PleaseFillIn
  let subst_then_run _ _ _ _ = raise PleaseFillIn

  let inst rel clo cells =
    let ExtClo {bnd; env} = clo in
    let Tm.NB (_, (ty, sys)) = bnd in
    let env' = env <>< cells in
    let vty = Syn.eval rel env' ty in
    let vsys = Syn.eval_tm_sys rel env' sys in
    vty, vsys

  let inst' rel clo cells =
    let vty, vsys = inst rel clo cells in
    Delay.make vty, vsys
end


and Env :
sig
  include Domain with type t = env
end =
struct
  type t = env
  let swap _ _ = raise PleaseFillIn
  let subst _ _ = raise PleaseFillIn
  let run _ _ = raise PleaseFillIn
  let subst_then_run _ _ = raise PleaseFillIn
end

and Con :
sig
  include DomainPlug with type t = con
end =
struct
  module Val = DelayedPlug (Con)
  module LazyVal = DelayedPlug (LazyPlug (Con))
  module ConSys = Sys (Con)
  module ConFace = Face (Con)
  module AbsSys = Sys (AbsPlug (Con))

  type t = con
  let swap _ _ = raise PleaseFillIn
  let subst _ _ = raise PleaseFillIn
  let plug _ _ _ = raise PleaseFillIn
  let subst_then_run _ _ _ _ = raise PleaseFillIn

  let rec run rel =
    function
    | Pi info ->
      let dom = Val.run rel info.dom in
      let cod = Clo.run rel info.cod in
      Pi {dom; cod}

    | Sg info ->
      let dom = Val.run rel info.dom in
      let cod = Clo.run rel info.cod in
      Sg {dom; cod}

    | Ext extclo ->
      let extclo = ExtClo.run rel extclo in
      Ext extclo

    | Neu info ->
      begin
        match ConSys.run rel info.sys with
        | sys ->
          let neu = Neu.run rel info.neu in
          let ty = Val.run rel info.ty in
          Neu {ty; neu; sys}
        | exception ConSys.Triv v ->
          v
      end

    | Lam clo ->
      let clo = Clo.run rel clo in
      Lam clo

    | ExtLam nclo ->
      let nclo = NClo.run rel nclo in
      ExtLam nclo

    | Cons (v0, v1) ->
      let v0 = Val.run rel v0 in
      let v1 = Val.run rel v1 in
      Cons (v0, v1)

    | Coe info ->
      begin
        match Rel.compare info.r info.r' rel with
        | `Same ->
          Val.run_then_out rel info.cap
        | _ ->
          let ty = CoeShape.run rel info.ty in
          let cap = Val.run rel info.cap in
          Coe {info with ty; cap}
      end

    | HCom info ->
      begin
        match Rel.compare info.r info.r' rel with
        | `Same ->
          Val.run_then_out rel info.cap
        | _ ->
          match AbsSys.run rel info.sys with
          | sys ->
            let cap = Val.run rel info.cap in
            let ty = HComShape.run rel info.ty in
            HCom {info with ty; cap; sys}

          | exception (AbsSys.Triv abs) ->
            let Abs (x, vx) = abs in
            hsubst info.r' x rel vx
      end

  and plug rel frm hd =
    match frm, hd with
    | FunApp arg, Lam clo ->
      Clo.inst rel clo @@ Val (Delay.make @@ lazy begin Val.out arg end)

    | FunApp arg, Coe {r; r'; ty = `Pi abs; cap} ->
      let Abs (x, quantx) = abs in
      let y, pi = Perm.freshen_name x in
      let dom = Abs (x, quantx.dom) in
      let coe_arg s = make_coe rel r' s dom arg in
      let coe_r'y = Delay.make @@ lazy begin coe_arg @@ `Atom y end in
      let cod_y = swap pi quantx.cod in
      let cod_coe = Abs (y, Delay.make @@ Clo.inst rel cod_y @@ Val coe_r'y) in
      rigid_coe rel r r' cod_coe @@
      Val.plug rel (FunApp (Delay.make @@ coe_arg r)) cap

    | FunApp arg, HCom {r; r'; ty = `Pi quant; cap; sys} ->
      let ty = Clo.inst rel quant.cod @@ Val (Delay.make @@ lazy begin Val.out arg end) in
      let cap = Val.plug rel frm cap in
      let sys = AbsSys.plug rel frm sys in
      rigid_hcom rel r r' ty cap sys

    | ExtApp rs, ExtLam nclo ->
      NClo.inst rel nclo @@ List.map (fun r -> Dim r) rs

    | ExtApp ss, Coe {r; r'; ty = `Ext abs; cap} ->
      let Abs (y, extclo_y) = abs in
      let ty_ss, sys_ss = ExtClo.inst rel extclo_y @@ List.map (fun x -> Dim x) ss in
      (* favonia: I commented out the following line because I'm not sure whether
       * the best interface should be values or cons.
       *
       * let sys_ss' = ValSys.forall y sys_ss in *)
      raise PleaseFillIn

    | ExtApp rs, HCom {r; r'; ty = `Ext qu; cap; sys} ->
      raise PleaseFillIn

    | Car, Cons (v0, _) ->
      Val.out v0

    | Car, Coe {r; r'; ty = `Sg abs; cap} ->
      let cap = Val.plug rel Car cap in
      let ty =
        let Abs (xs, {dom; cod}) = abs in
        Abs (xs, dom)
      in
      rigid_coe rel r r' ty cap

    | Cdr, Cons (_, v1) ->
      Val.out v1

    | _, Neu info ->
      let neu = Neu.plug rel frm info.neu in
      let sys = ConSys.plug rel frm info.sys in
      let ty, sys' = plug_ty rel frm info.ty hd in
      Neu {ty; neu; sys = sys' @ sys}

    | _ ->
      raise PleaseFillIn

  and make_coe rel r r' (abs : value abs) (cap : value) =
    match Rel.compare r r' rel with
    | `Same ->
      Val.out cap
    | _ ->
      rigid_coe rel r r' abs cap

  and make_hcom rel r r' ty cap sys =
    match Rel.compare r r' rel with
    | `Same ->
      Val.out cap
    | _ ->
      match AbsSys.run rel sys with
      | _ ->
        rigid_hcom rel r r' ty cap sys
      | exception (AbsSys.Triv abs) ->
        let Abs (x, vx) = abs in
        hsubst r' x rel vx


  (** Invariant: everything is already a value wrt. [rel], and it [r~>r'] is [rel]-rigid. *)
  and rigid_coe rel r r' abs cap : con =
    let Abs (x, tyx) = abs in
    match Val.out tyx with
    | Sg quant ->
      Coe {r; r'; ty = `Sg (Abs (x, quant)); cap}

    | Pi quant ->
      Coe {r; r'; ty = `Pi (Abs (x, quant)); cap}

    | Ext extclo ->
      Coe {r; r'; ty = `Ext (Abs (x, extclo)); cap}

    | Neu info ->
      let neu = {head = NCoe {r; r'; ty = Abs (x, info.neu); cap}; frames = Emp} in
      let ty = Val.hsubst r' x rel tyx in
      let sys =
        let cap_face = r, r', Delay.make @@ lazy begin Val.out cap end in
        let old_faces =
          flip ListUtil.filter_map info.sys @@ fun face ->
          flip Option.map (ConFace.forall x face) @@ fun (s, s', bdy) ->
          s, s',
          Delay.make @@
          lazy begin
            let rel' = Rel.equate' s s' rel in
            let abs = Abs (x, Delay.make @@ Lazy.force @@ LazyVal.run_then_out rel' bdy) in
            let cap = Val.run rel' cap in
            make_coe rel' r r' abs cap
          end
        in
        cap_face :: old_faces
      in
      Neu {ty; neu; sys}

    | _ -> raise PleaseFillIn

  and rigid_hcom rel r r' (ty : t) cap sys =
    match ty with
    | Sg quant ->
      HCom {r; r'; ty = `Sg quant; cap; sys}

    | Pi quant ->
      HCom {r; r'; ty = `Pi quant; cap; sys}

    | Ext extclo ->
      HCom {r; r'; ty = `Ext extclo; cap; sys}

    | Neu info ->
      raise PleaseFillIn
      (*
      let nhcom = NHCom {r; r'; cap; sys} in
      let neu = {info.neu with frames = info.neu.frames #< nhcom} in
      let neu_sys =
        let cap_face = r, r', lazy cap in
        let tube_faces =
          flip List.map sys @@ fun (s, s', abs) ->
          s, s',
          lazy begin
            let rel' = Rel.equate' s s' rel in
            let Abs (x, elx) = Lazy.force abs in
            hsubst rel' r' x elx
          end
        in
        let old_faces =
          flip List.map info.sys @@ fun (s, s', ty) ->
          s, s',
          match Rel.equate s s' rel with
          | `Changed rel' ->
            lazy begin
              let cap = run rel' cap in
              let ty = run rel' @@ Lazy.force ty in
              let sys = AbsSys.run rel' sys in
              make_hcom rel' r r' ty cap sys
            end
          | `Same ->
            lazy begin
              let ty = Lazy.force ty in
              make_hcom rel r r' ty cap sys
            end
        in
        cap_face :: tube_faces @ old_faces
      in
      Neu {ty; neu; sys = neu_sys}
      *)

    | _ ->
      raise PleaseFillIn

  and plug_ty rel frm ty hd =
    match Val.out ty, frm with
    | Pi {dom; cod}, FunApp arg ->
      let arg = lazy begin Val.out arg end in
      Delay.make @@ Clo.inst rel cod @@ Val (Delay.make arg), []

    | Ext extclo, ExtApp rs ->
      ExtClo.inst' rel extclo @@ List.map (fun r -> Dim r) rs

    | Sg {dom; _}, Car ->
      dom, []

    | Sg {dom; cod}, Cdr ->
      let car = lazy begin plug rel Car hd end in
      Delay.make @@ Clo.inst rel cod @@ Val (Delay.make car), []

    | _ ->
      raise PleaseFillIn

  and hsubst r x rel c =
    let rel' = Rel.subst' r x rel in
    subst_then_run rel' r x c
end

and CoeShape : Domain with type t = coe_shape =
struct
  type t = coe_shape

  module QAbs = Abs (Quantifier)
  module ECloAbs = Abs (ExtClo)

  let swap pi =
    function
    | `Pi abs -> `Pi (QAbs.swap pi abs)
    | `Sg abs -> `Sg (QAbs.swap pi abs)
    | `Ext abs -> `Ext (ECloAbs.swap pi abs)

  let subst r x =
    function
    | `Pi abs -> `Pi (QAbs.subst r x abs)
    | `Sg abs -> `Sg (QAbs.subst r x abs)
    | `Ext abs -> `Ext (ECloAbs.subst r x abs)

  let run rel =
    function
    | `Pi abs -> `Pi (QAbs.run rel abs)
    | `Sg abs -> `Sg (QAbs.run rel abs)
    | `Ext abs -> `Ext (ECloAbs.run rel abs)

  let subst_then_run rel r x =
    function
    | `Pi abs -> `Pi (QAbs.subst_then_run rel r x abs)
    | `Sg abs -> `Sg (QAbs.subst_then_run rel r x abs)
    | `Ext abs -> `Ext (ECloAbs.subst_then_run rel r x abs)
end

and HComShape : Domain with type t = hcom_shape =
struct
  type t = hcom_shape
  module Q = Quantifier

  let swap pi =
    function
    | `Pi qu -> `Pi (Q.swap pi qu)
    | `Sg qu -> `Sg (Q.swap pi qu)
    | `Ext clo -> `Ext (ExtClo.swap pi clo)
    | `Pos -> `Pos

  let subst r x =
    function
    | `Pi qu -> `Pi (Q.subst r x qu)
    | `Sg qu -> `Sg (Q.subst r x qu)
    | `Ext clo -> `Ext (ExtClo.subst r x clo)
    | `Pos -> `Pos

  let run rel =
    function
    | `Pi abs -> `Pi (Q.run rel abs)
    | `Sg abs -> `Sg (Q.run rel abs)
    | `Ext clo -> `Ext (ExtClo.run rel clo)
    | `Pos -> `Pos

  let subst_then_run rel r x =
    function
    | `Pi abs -> `Pi (Q.subst_then_run rel r x abs)
    | `Sg abs -> `Sg (Q.subst_then_run rel r x abs)
    | `Ext clo -> `Ext (ExtClo.subst_then_run rel r x clo)
    | `Pos -> `Pos
end

and Quantifier : Domain with type t = quantifier =
struct
  type t = quantifier
  let swap _ = raise PleaseFillIn
  let subst _ = raise PleaseFillIn
  let run _ = raise PleaseFillIn
  let subst_then_run _ = raise PleaseFillIn
end

and Neu : DomainPlug with type t = neu =
struct
  type t = neu

  let swap _ = raise PleaseFillIn
  let run _ = raise PleaseFillIn
  let subst _ = raise PleaseFillIn
  let subst_then_run _ = raise PleaseFillIn

  let plug rel frm neu =
    {neu with
     frames = neu.frames #< frm}
end

and Frame :
sig
  include Domain with type t = frame
  val occurs : Name.t bwd -> frame -> [`No | `Might]
end =
struct
  module Val = DelayedPlug (Con)
  module LazyCon = LazyPlug (Con)

  type t = frame

  let swap pi =
    function
    | FunApp arg ->
      let arg = Val.swap pi arg in
      FunApp arg
    | ExtApp rs ->
      let rs = List.map (Dim.swap pi) rs in
      ExtApp rs
    | Car | Cdr as frm ->
      frm
    | NHCom _ ->
      raise PleaseFillIn

  let subst r x =
    function
    | FunApp arg ->
      let arg = Val.subst r x arg in
      FunApp arg
    | ExtApp rs ->
      let rs = List.map (Dim.subst r x) rs in
      ExtApp rs
    | Car | Cdr as frm ->
      frm
    | NHCom _ ->
      raise PleaseFillIn

  let run rel =
    function
    | FunApp arg ->
      let arg = Val.run rel arg in
      FunApp arg
    | Car | Cdr | ExtApp _ as frm ->
      frm
    | NHCom _ ->
      raise PleaseFillIn

  let subst_then_run rel r x =
    function
    | FunApp arg ->
      let arg = Val.subst_then_run rel r x arg in
      FunApp arg
    | ExtApp rs as frm ->
      let rs = List.map (Dim.subst r x) rs in
      ExtApp rs
    | Car | Cdr as frm ->
      frm
    | NHCom _ ->
      raise PleaseFillIn

  let occurs xs =
    function
    | FunApp _ | ExtApp _ | NHCom _ ->
      `Might
    | Car | Cdr ->
      `No
end


and Sys :
  functor (X : DomainPlug) ->
  sig
    include DomainPlug with type t = X.t sys
    exception Triv of X.t

    val forall : Name.t -> t -> t
  end =
  functor (X : DomainPlug) ->
  struct
    type t = X.t sys
    module Face = Face (X)

    exception Triv of X.t

    let swap pi = List.map @@ Face.swap pi
    let subst r x = List.map @@ Face.subst r x

    let forall x = ListUtil.filter_map (Face.forall x)

    let run rel sys =
      let run_face face =
        try [Face.run rel face]
        with
        | Face.Dead -> []
        | Face.Triv bdy -> raise @@ Triv bdy
      in
      ListUtil.flat_map run_face sys

    let subst_then_run rel r x sys =
      let run_face face =
        try [Face.subst_then_run rel r x face]
        with
        | Face.Dead -> []
        | Face.Triv bdy -> raise @@ Triv bdy
      in
      ListUtil.flat_map run_face sys

    let plug rel frm sys =
      List.map (Face.plug rel frm) sys
  end

and Face :
  functor (X : DomainPlug) ->
  sig
    include DomainPlug with type t = X.t face

    val forall : Name.t -> t -> t option

    exception Triv of X.t
    exception Dead
  end =
  functor (X : DomainPlug) ->
  struct
    module DelayedLazyX = DelayedPlug (LazyPlug (X))

    type t = X.t face

    exception Triv of X.t
    exception Dead

    let forall x (r, r', bdy) =
      let sx = `Atom x in
      if r = sx || r' = sx then None else Some (r, r', bdy)

    let swap pi (r, r', bdy) =
      Dim.swap pi r, Dim.swap pi r',
      DelayedLazyX.swap pi bdy

    let subst r x (s, s', bdy) =
      Dim.subst r x s, Dim.subst r x s',
      DelayedLazyX.subst r x bdy

    let run rel (r, r', bdy) =
      match Rel.equate r r' rel with
      | `Same ->
        let bdy' = Lazy.force @@ DelayedLazyX.run_then_out rel bdy in
        raise @@ Triv bdy'
      | `Changed rel' ->
        r, r',
        DelayedLazyX.run rel' bdy
      | exception I.Inconsistent -> raise Dead

    let subst_then_run rel r x (s, s', bdy) =
      let s = Dim.subst r x s in
      let s' = Dim.subst r x s' in
      match Rel.equate s s' rel with
      | `Same ->
        let bdy' = Lazy.force @@ DelayedLazyX.subst_then_run_then_out rel r x bdy in
        raise @@ Triv bdy'
      | `Changed rel' ->
        s, s',
        DelayedLazyX.subst_then_run rel' r x bdy
      | exception I.Inconsistent -> raise Dead

    let plug rel frm (r, r', bdy) =
      let rel' = Rel.equate' r r' rel in
      r, r',
      let frm' = Frame.run rel' frm in
      DelayedLazyX.plug rel frm' bdy
  end

and Abs : functor (X : Domain) -> Domain with type t = X.t abs =
  functor (X : Domain) ->
  struct
    type t = X.t abs

    let swap pi abs =
      let Abs (x, a) = abs in
      let x' = Perm.swap_name pi x in
      let a' = X.swap pi a in
      Abs (x', a')

    let subst r z abs =
      let Abs (x, a) = abs in
      if z = x then abs else
        match r with
        | `Atom y when y = x ->
          let y, pi = Perm.freshen_name x in
          let a' = X.subst r z @@ X.swap pi a in
          Abs (y, a')
        | _ ->
          let a' = X.subst r z a in
          Abs (x, a')

    let run rel abs =
      let Abs (x, a) = abs in
      (* TODO: I think the following makes sense, but let's double check. The alternative is to freshen, but it seems like we don't need to if we can un-associate these names. *)
      let rel' = Rel.hide' x rel in
      let a' = X.run rel' a in
      Abs (x, a')

    (* XXX optimize this! *)
    let subst_then_run rel r x a =
      run rel @@ subst r x a
  end

and AbsPlug : functor (X : DomainPlug) -> DomainPlug with type t = X.t abs =
  functor (X : DomainPlug) ->
  struct
    module M = Abs(X)
    include M

    let plug rel frm abs =
      let Abs (x, a) = abs in
      match Frame.occurs (Emp #< x) frm with
      | `No ->
        let a' = X.plug rel frm a in
        Abs (x, a')
      | `Might ->
        let y, pi = Perm.freshen_name x in
        let rel' = Rel.hide' x rel in
        let a' = X.plug rel' frm @@ X.swap pi a in
        Abs (y, a')

  end

and DelayedPlug : DelayedDomainPlug =
  functor (X : DomainPlug) ->
  struct
    type t = X.t Delay.t

    let swap _ = raise PleaseFillIn
    let subst _ = raise PleaseFillIn
    let run _ = raise PleaseFillIn
    let subst_then_run _ = raise PleaseFillIn
    let plug _ = raise PleaseFillIn

    let force =
      Delay.fold @@ fun r d -> Delay.make' r (Lazy.force d)

    let out = Delay.out X.run

    let hsubst r x rel v = raise PleaseFillIn
    (*
      let rel' = Rel.subst' r x rel in
      subst_then_run rel' r x v
    *)
    let subst_then_run_then_out _ = raise PleaseFillIn
    let run_then_out rel _ = raise PleaseFillIn
  end

and LazyPlug : functor (X : DomainPlug) -> DomainPlug with type t = X.t Lazy.t =
  functor (X : DomainPlug) ->
  struct
    type t = X.t Lazy.t

    let swap _ _ = raise PleaseFillIn
    let subst _ _ _ = raise PleaseFillIn
    let run _ _ = raise PleaseFillIn
    let subst_then_run _ _ _ = raise PleaseFillIn
    let plug _ _ _ = raise PleaseFillIn
  end
