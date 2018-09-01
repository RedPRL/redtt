open RedBasis
open Bwd
open BwdNotation

exception PleaseFillIn

type dim = I.t

type 'a face = dim * dim * 'a Lazy.t
type 'a sys = 'a face list
type 'a abs = Abs of Name.t * 'a

(** This is the type of "prevalues", that is the domain from which values come.
    A prevalue can be judged to be a value with respect to a restriction / dimension
    theory. I think we will not write code that checks that something is a value, but instead
    make this involved in the pre-and-post- conditions of the semantic operations. *)
type value =
  | Pi of quantifier
  | Sg of quantifier
  | Ext of ext_clo

  | Lam of clo
  | ExtLam of nclo
  | Cons of value * value
  | Coe of {r : dim; r' : dim; ty : coe_shape; cap : value}
  | HCom of {r : dim; r' : dim; ty : hcom_shape; cap : value; sys : value abs sys}
  | Neu of {ty : value; neu : neu; sys : value sys}

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
  | NHCom of {r : dim; r' : dim; cap : value; sys : value abs sys}

and neu =
  {head : head;
   frames : frame bwd}

and cell =
  | Val of value Lazy.t
  | Dim of dim Lazy.t

and env = cell bwd

and clo = Clo of {bnd : Tm.tm Tm.bnd; env : env}
and nclo = NClo of {bnd : Tm.tm Tm.nbnd; env : env}
and ext_clo = ExtClo of {bnd : (Tm.tm * (Tm.tm, Tm.tm) Tm.system) Tm.nbnd; env : env}


let flip f x y = f y x


(** This should be the dimension equality oracle *)
module Rel = IDisjointSet.Make (RedBasis.PersistentTable.M)

(** Permutations *)
module Perm :
sig
  type t
  val freshen_name : Name.t -> Name.t * t
  val freshen_names : Name.t bwd -> Name.t bwd * t
  val swap_name : t -> Name.t -> Name.t
end =
struct
  type t
  let freshen_name _ = raise PleaseFillIn
  let freshen_names _ = raise PleaseFillIn
  let swap_name _ = raise PleaseFillIn
end

type rel = Rel.t
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
end

module type DomainPlug =
sig
  include Domain

  (** Plug applies a stack frame to an element of the domain. *)
  val plug : rel -> frame -> t -> t
end



module rec Syn :
sig
  type t = Tm.tm
  val eval : rel -> env -> t -> value
  val eval_tm_sys : rel -> env -> (t, t) Tm.system -> value sys
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
end

and Clo :
sig
  include Domain with type t = clo
  val inst : rel -> t -> cell -> value
end =
struct
  type t = clo

  let swap _ _ = raise PleaseFillIn
  let subst _ _ = raise PleaseFillIn
  let run _ _ = raise PleaseFillIn

  let inst rel clo cell =
    let Clo {bnd; env} = clo in
    let Tm.B (_, tm) = bnd in
    Syn.eval rel (env #< cell) tm
end

and NClo :
sig
  include Domain with type t = nclo
  val inst : rel -> t -> cell list -> value
end =
struct
  type t = nclo

  let swap _ _ = raise PleaseFillIn
  let subst _ _ = raise PleaseFillIn
  let run _ _ = raise PleaseFillIn

  let inst (rel : rel) nclo cells : value =
    let NClo {bnd; env} = nclo in
    let Tm.NB (_, tm) = bnd in
    Syn.eval rel (env <>< cells) tm
end

and ExtClo :
sig
  include Domain with type t = ext_clo
  val inst : rel -> t -> cell list -> value * value sys
end =
struct
  type t = ext_clo

  let swap _ _ = raise PleaseFillIn
  let subst _ _ = raise PleaseFillIn
  let run _ _ = raise PleaseFillIn

  let inst rel clo cells =
    let ExtClo {bnd; env} = clo in
    let Tm.NB (_, (ty, sys)) = bnd in
    let env' = env <>< cells in
    let vty = Syn.eval rel env' ty in
    let vsys = Syn.eval_tm_sys rel env' sys in
    vty, vsys
end


and Env : Domain with type t = env =
struct
  type t = env
  let swap _ _ = raise PleaseFillIn
  let subst _ _ = raise PleaseFillIn
  let run _ _ = raise PleaseFillIn
end

and Val : DomainPlug with type t = value =
struct
  type t = value

  module ValSys = Sys (Val)
  module ValFace = Face (Val)
  module AbsSys = Sys (AbsPlug (Val))

  let swap _ _ = raise PleaseFillIn
  let subst _ _ _ = raise PleaseFillIn


  let rec run rel =
    function
    | Pi info ->
      let dom = run rel info.dom in
      let cod = Clo.run rel info.cod in
      Pi {dom; cod}

    | Sg info ->
      let dom = run rel info.dom in
      let cod = Clo.run rel info.cod in
      Sg {dom; cod}

    | Ext extclo ->
      let extclo = ExtClo.run rel extclo in
      Ext extclo

    | Neu info ->
      begin
        match ValSys.run rel info.sys with
        | sys ->
          let neu = Neu.run rel info.neu in
          let ty = run rel info.ty in
          Neu {ty; neu; sys}
        | exception ValSys.Triv v -> v
      end

    | Lam clo ->
      let clo = Clo.run rel clo in
      Lam clo

    | ExtLam nclo ->
      let nclo = NClo.run rel nclo in
      ExtLam nclo

    | Cons (v0, v1) ->
      let v0 = run rel v0 in
      let v1 = run rel v1 in
      Cons (v0, v1)

    | Coe info ->
      begin
        match Rel.compare info.r info.r' rel with
        | `Same ->
          run rel info.cap
        | _ ->
          let ty = CoeShape.run rel info.ty in
          let cap = run rel info.cap in
          Coe {info with ty; cap}
      end

    | HCom info ->
      begin
        match Rel.compare info.r info.r' rel with
        | `Same ->
          run rel info.cap
        | _ ->
          match AbsSys.run rel info.sys with
          | sys ->
            let cap = run rel info.cap in
            let ty = HComShape.run rel info.ty in
            HCom {info with ty; cap; sys}

          | exception (AbsSys.Triv abs) ->
            let Abs (x, vx) = abs in
            hsubst rel info.r' x vx
      end

  and plug rel frm hd =
    match frm, hd with
    | FunApp arg, Lam clo ->
      Clo.inst rel clo @@ Val (lazy arg)

    | FunApp arg, Coe {r; r'; ty = `Pi abs; cap} ->
      let Abs (x, quantx) = abs in
      let y, pi = Perm.freshen_name x in
      let dom = Abs (x, quantx.dom) in
      let coe_arg s = make_coe rel r' s dom arg in
      let coe_r'y = lazy begin coe_arg @@ `Atom y end in
      let cod_y = swap pi quantx.cod in
      let cod_coe = Abs (y, Clo.inst rel cod_y @@ Val coe_r'y) in
      rigid_coe rel r r' cod_coe @@
      plug rel (FunApp (coe_arg r)) cap

    | FunApp arg, HCom {r; r'; ty = `Pi quant; cap; sys} ->
      let ty = Clo.inst rel quant.cod @@ Val (lazy arg) in
      let cap = plug rel frm cap in
      let sys = AbsSys.plug rel frm sys in
      rigid_hcom rel r r' ty cap sys

    | ExtApp rs, ExtLam nclo ->
      NClo.inst rel nclo @@ List.map (fun r -> Dim (lazy r)) rs

    | ExtApp rs, Coe {r; r'; ty = `Ext abs; cap} ->
      raise PleaseFillIn

    | ExtApp rs, HCom {r; r'; ty = `Ext qu; cap; sys} ->
      raise PleaseFillIn


    | Car, Cons (v0, _) ->
      v0

    | Car, Coe {r; r'; ty = `Sg abs; cap} ->
      let cap = plug rel Car cap in
      let ty =
        let Abs (xs, {dom; cod}) = abs in
        Abs (xs, dom)
      in
      rigid_coe rel r r' ty cap

    | Cdr, Cons (_, v1) ->
      v1

    | _, Neu info ->
      let neu = Neu.plug rel frm info.neu in
      let sys = ValSys.plug rel frm info.sys in
      let ty, sys' = plug_ty rel frm info.ty hd in
      Neu {ty; neu; sys = sys' @ sys}

    | _ ->
      raise PleaseFillIn

  and plug_ty rel frm ty hd =
    match ty, frm with
    | Pi {dom; cod}, FunApp arg ->
      Clo.inst rel cod @@ Val (lazy arg), []

    | Ext extclo, ExtApp rs ->
      ExtClo.inst rel extclo @@ List.map (fun r -> Dim (lazy r)) rs

    | Sg {dom; _}, Car ->
      dom, []

    | Sg {dom; cod}, Cdr ->
      let car = plug rel Car hd in
      Clo.inst rel cod @@ Val (lazy car), []

    | _ ->
      raise PleaseFillIn

  and make_coe rel r r' abs cap =
    match Rel.compare r r' rel with
    | `Same ->
      cap
    | _ ->
      rigid_coe rel r r' abs cap

  and make_hcom rel r r' ty cap sys =
    match Rel.compare r r' rel with
    | `Same ->
      cap
    | _ ->
      match AbsSys.run rel sys with
      | _ ->
        rigid_hcom rel r r' ty cap sys
      | exception (AbsSys.Triv abs) ->
        let Abs (x, vx) = abs in
        hsubst rel r' x vx


  (** Invariant: everything is already a value wrt. [rel], and it [r~>r'] is [rel]-rigid. *)
  and rigid_coe rel r r' abs cap : value =
    let Abs (x, tyx) = abs in
    match tyx with
    | Sg quant ->
      Coe {r; r'; ty = `Sg (Abs (x, quant)); cap}

    | Pi quant ->
      Coe {r; r'; ty = `Pi (Abs (x, quant)); cap}

    | Ext extclo ->
      Coe {r; r'; ty = `Ext (Abs (x, extclo)); cap}

    | Neu info ->
      let neu = {head = NCoe {r; r'; ty = Abs (x, info.neu); cap}; frames = Emp} in
      let ty = hsubst rel r' x tyx in
      let sys =
        let cap_face = r, r', lazy cap in
        let old_faces =
          flip ListUtil.filter_map info.sys @@ fun face ->
          flip Option.map (ValFace.forall x face) @@ fun (s, s', bdy) ->
          s, s',
          lazy begin
            let rel' = Rel.union s s' rel in
            let abs = Abs (x, run rel' @@ Lazy.force bdy) in
            let cap = run rel' cap in
            make_coe rel' r r' abs cap
          end
        in
        cap_face :: old_faces
      in
      Neu {ty; neu; sys}

    | _ -> raise PleaseFillIn

  and rigid_hcom rel r r' ty cap sys =
    match ty with
    | Sg quant ->
      HCom {r; r'; ty = `Sg quant; cap; sys}

    | Pi quant ->
      HCom {r; r'; ty = `Pi quant; cap; sys}

    | Ext extclo ->
      HCom {r; r'; ty = `Ext extclo; cap; sys}

    | Neu info ->
      let nhcom = NHCom {r; r'; cap; sys} in
      let neu = {info.neu with frames = info.neu.frames #< nhcom} in
      let neu_sys =
        let cap_face = r, r', lazy cap in
        let tube_faces =
          flip List.map sys @@ fun (s, s', abs) ->
          s, s',
          lazy begin
            let rel' = Rel.union s s' rel in
            let Abs (x, elx) = Lazy.force abs in
            hsubst rel' r' x elx
          end
        in
        let old_faces =
          flip List.map info.sys @@ fun (s, s', ty) ->
          s, s',
          lazy begin
            let rel' = Rel.union s s' rel in
            let cap = run rel' cap in
            let ty = run rel' @@ Lazy.force ty in
            let sys = AbsSys.run rel' sys in
            make_hcom rel' r r' ty cap sys
          end
        in
        cap_face :: tube_faces @ old_faces
      in
      Neu {ty; neu; sys = neu_sys}

    | _ ->
      raise PleaseFillIn

  and hsubst rel r x v =
    let rel' = Rel.subst r x rel in
    run rel' @@ subst r x v
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
end

and Quantifier : Domain with type t = quantifier =
struct
  type t = quantifier
  let swap _ = raise PleaseFillIn
  let subst _ = raise PleaseFillIn
  let run _ = raise PleaseFillIn
end

and Neu : DomainPlug with type t = neu =
struct
  type t = neu

  let swap _ = raise PleaseFillIn
  let run _ = raise PleaseFillIn
  let subst _ = raise PleaseFillIn

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
    | Car | Cdr | ExtApp _ as frm->
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
    type t = X.t face

    exception Triv of X.t
    exception Dead

    let forall x (r, r', bdy) =
      let sx = `Atom x in
      if r = sx || r' = sx then None else Some (r, r', bdy)

    let swap pi (r, r', bdy) =
      Dim.swap pi r, Dim.swap pi r',
      lazy begin X.swap pi @@ Lazy.force bdy end

    let subst r x (s, s', bdy) =
      Dim.subst r x s, Dim.subst r x s',
      lazy begin X.subst r x @@ Lazy.force bdy end

    let run rel (r, r', bdy) =
      match Rel.compare r r' rel with
      | `Apart ->
        raise Dead
      | `Same ->
        let bdy' = X.run rel @@ Lazy.force bdy in
        raise @@ Triv bdy'
      | `Indet ->
        r, r',
        lazy begin
          let rel' = Rel.union r r' rel in
          X.run rel' @@ Lazy.force bdy
        end

    let plug rel frm (r, r', bdy) =
      let rel' = Rel.union r r' rel in
      r, r',
      lazy begin
        let frm' = Frame.run rel' frm in
        X.plug rel frm' @@ Lazy.force bdy
      end
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
      let rel' = Rel.hide x rel in
      let a' = X.run rel' a in
      Abs (x, a')
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
        let rel' = Rel.hide x rel in
        let a' = X.plug rel' frm @@ X.swap pi a in
        Abs (y, a')

  end
