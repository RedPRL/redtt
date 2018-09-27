open RedBasis
open Bwd
open BwdNotation

exception PleaseFillIn
exception PleaseRaiseProperError

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
  val unleash : (rel -> 'a -> 'a) -> 'a t -> 'a

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

  let unleash f v =
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
  | Fst
  | Snd
  | NHCom of {r : dim; r' : dim; cap : value; sys : con abs sys}

and neu =
  {head : head;
   frames : frame bwd}

and cell =
  | Val of con Lazy.t Delay.t
  | Dim of dim

and env = {cells : cell bwd; n_minus_one : int}

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
  val fold : (Name.t -> Name.t -> 'a -> 'a) -> t -> 'a -> 'a
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
  let fold f = List.fold_right (fun (x, x') a -> f x x' a)
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
  val unleash : t -> X.t

  (* a convenience function that is hopefully self-explanatory and more optimized *)
  val run_then_unleash : rel -> t -> X.t
end

module rec Syn :
sig
  type t = Tm.tm
  exception Triv of con
  val eval : rel -> env -> t -> con
  val eval_dim : env -> t -> dim
  val eval_tm_sys : rel -> env -> (t, t) Tm.system -> con sys
end =
struct
  type t = Tm.tm

  exception Triv of con

  module LazyValue = DelayedPlug (LazyPlug (Con))

  let rec eval_dim env t =
    match Tm.unleash t with
    | Tm.Dim0 -> `Dim0
    | Tm.Dim1 -> `Dim1
    | Tm.Up (Tm.Ix (i, _), Emp) ->
      begin
        match Env.lookup_cell_by_index i env with
        | Dim r -> r
        | _ -> raise PleaseRaiseProperError
      end
    | Tm.Up (Tm.Var _, Emp) -> raise PleaseFillIn
    | Tm.Up (Tm.DownX r, Emp) -> eval_dim env r
    | _ -> raise PleaseRaiseProperError

  let rec eval rel env t =
    match Tm.unleash t with
    | Tm.Pi (dom, cod) ->
      let dom = Delay.make @@ eval rel env dom in
      let cod = Clo {bnd = cod; env} in
      Pi {dom; cod}

    | Tm.Sg (dom, cod) ->
      let dom = Delay.make @@ eval rel env dom in
      let cod = Clo {bnd = cod; env} in
      Sg {dom; cod}

    | Tm.Ext bnd ->
      Ext (ExtClo {bnd; env})

    | Tm.Lam bnd ->
      Lam (Clo {bnd; env})

    | Tm.ExtLam bnd ->
      ExtLam (NClo {bnd; env})

    | Tm.Cons (t0, t1) ->
      let v0 = Delay.make @@ eval rel env t0 in
      let v1 = Delay.make @@ eval rel env t1 in
      Cons (v0, v1)

    | Tm.Up (hd, spine) ->
      eval_cmd rel env hd spine

    | _ -> raise PleaseFillIn

  and eval_cmd rel env hd sp =
    let vhd = eval_head rel env hd in
    eval_spine rel env vhd sp

  and eval_spine rel env vhd =
    function
    | Emp -> vhd
    | Snoc (sp, frm) ->
      let v = eval_spine rel env vhd sp in
      let frm = eval_frame rel env frm in
      Con.plug rel frm vhd

  and eval_frame rel env =
    function
    | Tm.Fst -> Fst
    | Tm.Snd -> Snd
    | Tm.FunApp t -> FunApp (Delay.make @@ eval rel env t)
    | Tm.ExtApp l -> ExtApp (List.map (eval_dim env) l)
    | _ -> raise PleaseFillIn

  and eval_bnd rel env =
    function
    | Tm.B (nm, tm) ->
      let x = Name.named nm in
      let env = Env.extend_cell (Dim (`Atom x)) env in
      Abs (x, Delay.make @@ eval rel env tm)

  and eval_head rel env =
    function
    | Tm.Down info ->
      eval rel env info.tm

    | Tm.Coe info ->
      let r = eval_dim env info.r in
      let r' = eval_dim env info.r' in
      let abs = eval_bnd rel env info.ty  in
      let cap = Delay.make @@ eval rel env info.tm in
      Con.make_coe rel r r' ~abs ~cap

    | Tm.HCom info ->
      let r = eval_dim env info.r in
      let r' = eval_dim env info.r' in
      let ty = eval rel env info.ty in
      let cap = Delay.make @@ eval rel env info.cap in
      let sys = eval_bnd_sys rel env info.sys in
      Con.make_hcom rel r r' ~ty ~cap ~sys

    | Tm.Ix (i, _) ->
      begin
        match Env.lookup_cell_by_index i env with
        | Val v -> Lazy.force @@ LazyValue.unleash v
        | _ -> raise PleaseRaiseProperError
      end

    | _ -> raise PleaseFillIn

  and eval_bnd_sys _ _ = raise PleaseFillIn
  and eval_tm_sys _ _ = raise PleaseFillIn
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
    Syn.eval rel (Env.extend_cell cell env) tm
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
    Syn.eval rel (Env.extend_cells cells env) tm
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
    let env' = Env.extend_cells cells env in
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

  val emp : unit -> env
  val extend_cell : cell -> env -> env
  val extend_cells : cell list -> env -> env
  val lookup_cell_by_index : int -> env -> cell
  val index_of_level : env -> int -> int
  val level_of_index : env -> int -> int
end =
struct
  type t = env
  let swap _ _ = raise PleaseFillIn
  let subst _ _ = raise PleaseFillIn
  let run _ _ = raise PleaseFillIn
  let subst_then_run _ _ = raise PleaseFillIn

  let emp () = {cells = Emp; n_minus_one = -1}

  let lookup_cell_by_index i {cells; _} = Bwd.nth cells i

  let extend_cells cells env =
    {cells = env.cells <>< cells;
     n_minus_one = env.n_minus_one + List.length cells}

  let extend_cell cell env =
    extend_cells [cell] env

  let index_of_level {n_minus_one; _} i = n_minus_one - i
  let level_of_index {n_minus_one; _} i = n_minus_one - i
end

and Con :
sig
  include DomainPlug with type t = con
  val make_coe : rel -> dim -> dim -> abs:value abs -> cap:value -> con
  val make_hcom : rel -> dim -> dim -> ty:con -> cap:value -> sys:con abs sys -> con
end =
struct
  module ConSys = Sys (Con)
  module ConFace = Face (Con)
  module ConAbsFace = Face (AbsPlug (Con))
  module ConAbsSys = Sys (AbsPlug (Con))
  module Val = DelayedPlug (Con)
  module ValAbs = AbsPlug (Val)

  type t = con
  let swap _ _ = raise PleaseFillIn
  let subst _ _ _ = raise PleaseFillIn
  let plug _ _ _ = raise PleaseFillIn

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
          Val.run_then_unleash rel info.cap
        | _ ->
          let ty = CoeShape.run rel info.ty in
          let cap = Val.run rel info.cap in
          Coe {info with ty; cap}
      end

    | HCom info ->
      begin
        match Rel.compare info.r info.r' rel with
        | `Same ->
          Val.run_then_unleash rel info.cap
        | _ ->
          match ConAbsSys.run rel info.sys with
          | sys ->
            let cap = Val.run rel info.cap in
            let ty = HComShape.run rel info.ty in
            HCom {info with ty; cap; sys}

          | exception (ConAbsSys.Triv abs) ->
            let Abs (x, vx) = abs in
            hsubst info.r' x rel vx
      end

  and plug rel frm hd =
    match frm, hd with
    | FunApp arg, Lam clo ->
      Clo.inst rel clo @@ Val (Delay.make @@ lazy begin Val.unleash arg end)

    | FunApp arg, Coe {r; r'; ty = `Pi abs; cap} ->
      let Abs (x, quantx) = abs in
      let y, pi = Perm.freshen_name x in
      let dom = Abs (x, quantx.dom) in
      let coe_arg s = make_coe rel r' s ~abs:dom ~cap:arg in
      let coe_r'y = Delay.make @@ lazy begin coe_arg @@ `Atom y end in
      let cod_y = swap pi quantx.cod in
      let cod_coe = Abs (y, Delay.make @@ Clo.inst rel cod_y @@ Val coe_r'y) in
      rigid_coe rel r r' cod_coe @@
      Val.plug rel (FunApp (Delay.make @@ coe_arg r)) cap

    | FunApp arg, HCom {r; r'; ty = `Pi quant; cap; sys} ->
      let ty = Clo.inst rel quant.cod @@ Val (Delay.make @@ lazy begin Val.unleash arg end) in
      let cap = Val.plug rel frm cap in
      let sys = ConAbsSys.plug rel frm sys in
      rigid_hcom rel r r' ty cap sys

    | ExtApp rs, ExtLam nclo ->
      NClo.inst rel nclo @@ List.map (fun r -> Dim r) rs

    | ExtApp ss, Coe {r; r'; ty = `Ext abs; cap} ->
      let Abs (y, extclo_y) = abs in
      let ty_ss, sys_ss = ExtClo.inst (Rel.hide' y rel) extclo_y @@ List.map (fun x -> Dim x) ss in
      let sys_ss' = ConSys.forall y sys_ss in
      raise PleaseFillIn

    | ExtApp rs, HCom {r; r'; ty = `Ext qu; cap; sys} ->
      raise PleaseFillIn

    | Fst, Cons (v0, _) ->
      Val.unleash v0

    | Fst, Coe {r; r'; ty = `Sg abs; cap} ->
      let cap = Val.plug rel Fst cap in
      let ty =
        let Abs (xs, {dom; cod}) = abs in
        Abs (xs, dom)
      in
      rigid_coe rel r r' ty cap

    | Snd, Cons (_, v1) ->
      Val.unleash v1

    | _, Neu info ->
      let neu = Neu.plug rel frm info.neu in
      let sys = ConSys.plug rel frm info.sys in
      let ty, sys' = plug_ty rel frm info.ty hd in
      Neu {ty; neu; sys = sys' @ sys}

    | _ ->
      raise PleaseFillIn

  and make_coe rel r r' ~abs ~cap =
    match Rel.compare r r' rel with
    | `Same ->
      Val.unleash cap
    | _ ->
      rigid_coe rel r r' abs cap

  and make_hcom rel r r' ~ty ~cap ~sys =
    match Rel.compare r r' rel with
    | `Same ->
      Val.unleash cap
    | _ ->
      match ConAbsSys.run rel sys with
      | _ ->
        rigid_hcom rel r r' ty cap sys
      | exception (ConAbsSys.Triv abs) ->
        let Abs (x, vx) = abs in
        hsubst r' x rel vx


  (** Invariant: everything is already a value wrt. [rel], and it [r~>r'] is [rel]-rigid. *)
  and rigid_coe rel r r' abs cap : con =
    let Abs (x, tyx) = abs in
    match Val.unleash tyx with
    | Sg quant ->
      Coe {r; r'; ty = `Sg (Abs (x, quant)); cap}

    | Pi quant ->
      Coe {r; r'; ty = `Pi (Abs (x, quant)); cap}

    | Ext extclo ->
      Coe {r; r'; ty = `Ext (Abs (x, extclo)); cap}

    | Neu info ->
      let neu = {head = NCoe {r; r'; ty = Abs (x, info.neu); cap}; frames = Emp} in
      let ty = Val.subst_then_run (Rel.hide' x rel) r x tyx in
      let sys =
        let cap_face = r, r', Delay.make @@ lazy begin Val.unleash cap end in
        let old_faces =
          ConSys.foreach_forall x info.sys @@ ConFace.map_run @@ fun (s, s', bdy) ->
          lazy begin
            let rel' = Rel.equate' s s' rel in
            let abs = ValAbs.run rel' @@ Abs (x, Delay.make @@ Lazy.force bdy) in
            let cap = Val.run rel' cap in
            make_coe rel' r r' ~abs ~cap
          end
        in
        cap_face :: old_faces
      in
      Neu {ty; neu; sys}

    | _ -> raise PleaseFillIn

  and rigid_hcom rel r r' (ty : con) cap sys =
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
        let cap_face = r, r', Delay.make @@ lazy begin Val.unleash cap end in
        let tube_faces =
          ListUtil.foreach sys @@ ConAbsFace.map_run @@ fun (s, s', abs) ->
          lazy begin
            let rel' = Rel.equate' s s' rel in
            let Abs (x, elx) = Lazy.force abs in
            hsubst r' x rel' elx
          end
        in
        let old_faces =
          ListUtil.foreach info.sys @@ ConFace.map_run @@ fun (s, s', ty) ->
          lazy begin
            let rel' = Rel.equate' s s' rel in
            let cap = Val.run rel' cap in
            let ty = run rel' @@ Lazy.force ty in
            let sys = ConAbsSys.run rel' sys in
            make_hcom rel' r r' ~ty ~cap ~sys
          end
        in
        cap_face :: tube_faces @ old_faces
      in
      Neu {ty = Delay.make ty; neu; sys = neu_sys}

    | _ ->
      raise PleaseFillIn

  and plug_ty rel frm ty hd =
    match Val.unleash ty, frm with
    | Pi {dom; cod}, FunApp arg ->
      let arg = lazy begin Val.unleash arg end in
      Delay.make @@ Clo.inst rel cod @@ Val (Delay.make arg), []

    | Ext extclo, ExtApp rs ->
      ExtClo.inst' rel extclo @@ List.map (fun r -> Dim r) rs

    | Sg {dom; _}, Fst ->
      dom, []

    | Sg {dom; cod}, Snd ->
      let car = lazy begin plug rel Fst hd end in
      Delay.make @@ Clo.inst rel cod @@ Val (Delay.make car), []

    | _ ->
      raise PleaseFillIn

  and hsubst r x rel c =
    let rel' = Rel.subst' r x rel in
    subst_then_run rel' r x c

  and subst_then_run rel r x c =
    run rel @@ subst r x c
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

  type t = frame

  let swap pi =
    function
    | FunApp arg ->
      let arg = Val.swap pi arg in
      FunApp arg
    | ExtApp rs ->
      let rs = List.map (Dim.swap pi) rs in
      ExtApp rs
    | Fst | Snd as frm ->
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
    | Fst | Snd as frm ->
      frm
    | NHCom _ ->
      raise PleaseFillIn

  let run rel =
    function
    | FunApp arg ->
      let arg = Val.run rel arg in
      FunApp arg
    | Fst | Snd | ExtApp _ as frm ->
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
    | Fst | Snd as frm ->
      frm
    | NHCom _ ->
      raise PleaseFillIn

  let occurs xs =
    function
    | FunApp _ | ExtApp _ | NHCom _ ->
      `Might
    | Fst | Snd ->
      `No
end


and Sys :
  functor (X : DomainPlug) ->
  sig
    include DomainPlug with type t = X.t sys
    exception Triv of X.t

    val forall : Name.t -> t -> t

    (* convenience function *)
    val foreach_forall : Name.t -> t -> (X.t face -> 'b) -> 'b list
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

    let foreach_forall x sys f =
      ListUtil.filter_map (fun face -> Option.map f (Face.forall x face)) sys
  end

and Face :
  functor (X : DomainPlug) ->
  sig
    include DomainPlug with type t = X.t face

    exception Triv of X.t
    exception Dead

    val forall : Name.t -> t -> t option

    (* a map for hooking up `run` *)
    val map_run : (dim * dim * X.t Lazy.t -> 'a Lazy.t) -> t -> 'a face
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

    let map_run f (r, r', bdy) =
      (r, r', Delay.make @@ f (r, r', Delay.drop_rel bdy))

    let swap pi (r, r', bdy) =
      Dim.swap pi r, Dim.swap pi r',
      DelayedLazyX.swap pi bdy

    let subst r x (s, s', bdy) =
      Dim.subst r x s, Dim.subst r x s',
      DelayedLazyX.subst r x bdy

    let run rel (r, r', bdy) =
      match Rel.equate r r' rel with
      | `Same ->
        let bdy' = X.run rel (Lazy.force @@ Delay.drop_rel bdy) in
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
        let bdy' = X.subst_then_run rel r x (Lazy.force @@ Delay.drop_rel bdy) in
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

    let unleash = Delay.unleash X.run

    let swap pi = Delay.fold @@ fun rel v ->
      Delay.make' (Option.map (Perm.fold Rel.swap pi) rel) (X.swap pi v)
    let subst r x = Delay.fold @@ fun rel v ->
      Delay.make' (Option.map (Rel.subst' r x) rel) (X.subst r x v)
    let run rel v = Delay.with_rel rel v
    let subst_then_run rel r x v = Delay.make' (Some rel) (X.subst r x (Delay.drop_rel v))

    (* it is safe to `unleash v` here, but maybe we can do `Delay.drop_rel v`? *)
    let plug rel frm v = Delay.make @@ X.plug rel frm (unleash v)

    let run_then_unleash rel v = X.run rel (Delay.drop_rel v)
  end

and LazyPlug : functor (X : DomainPlug) -> DomainPlug with type t = X.t Lazy.t =
  functor (X : DomainPlug) ->
  struct
    type t = X.t Lazy.t

    let swap pi v = lazy begin X.swap pi (Lazy.force v) end
    let subst r x v = lazy begin X.subst r x (Lazy.force v) end
    let run rel v = lazy begin X.run rel (Lazy.force v) end
    let subst_then_run rel r x v = lazy begin X.subst_then_run rel r x (Lazy.force v) end
    let plug rel frm v = lazy begin X.plug rel frm (Lazy.force v) end
  end
