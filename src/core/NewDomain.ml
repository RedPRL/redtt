open RedBasis
open Bwd
open BwdNotation

exception PleaseFillIn
exception PleaseRaiseProperError
exception CanJonHelpMe
exception CanFavoniaHelpMe

type dim = I.t

(** The dimension equality oracle *)
module Rel = NewRestriction
type rel = Rel.t

(* this module provides the data type to hold an optional rel to
 * facilitate the dropping of `run phi1` in `run phi2 @@ run phi1 a`.
 *
 * the inner datatype is mutable in order to remember the result. *)
module Delayed :
sig
  type 'a t
  val make : 'a -> 'a t
  val make' : rel option -> 'a -> 'a t

  (* this is a brutal API to get the raw data out. the caller has
   * the responsibility to apply proper restrictions. *)
  val drop_rel : 'a t -> 'a

  (* this is a convenience function to create a new delayed X.run
   * with a new rel. *)
  val with_rel : rel -> 'a t -> 'a t

  (* this is to force the result. the first argument is intended
   * to be X.run where X is some structure implementing Domain. *)
  val unleash : (rel -> 'a -> 'a) -> 'a t -> 'a

  (* this is to expose the inner structure. the caller has
   * the responsibility to apply proper restrictions. *)
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

type 'a face = dim * dim * 'a Lazy.t Delayed.t
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
  | Cons of value * value
  | ExtLam of nclo

  | HCom of {r : dim; r' : dim; ty : hcom_shape; cap : value; sys : con abs sys}
  | Coe of {r : dim; r' : dim; ty : coe_shape; cap : value}
  | Com of {r : dim; r' : dim; ty : coe_shape; cap : value; sys : con abs sys}

  | Univ of {kind : Kind.t; lvl : Lvl.t}

  | V of {r : dim; ty0 : value; ty1 : value; equiv : value}
  | VIn of {r : dim; el0 : value; el1 : value}

  | Neu of {ty : value; neu : neu; sys : con sys}

and value = con Delayed.t

and quantifier =
  {dom : value;
   cod : clo}

and coe_shape =
  [ `Pi of quantifier abs   (** coe in pi *)
  | `Sg of quantifier abs   (** coe in sigma *)
  | `Ext of ext_clo abs     (** coe in extension type *)
  ]

and com_shape = coe_shape

and hcom_shape =
  [ `Pi of quantifier   (** hcom in pi *)
  | `Sg of quantifier   (** hcom in sigma *)
  | `Ext of ext_clo     (** hcom in extension type *)
  | `Pos                (** fhcom, i.e. hcom in positive types *)
  ]


and head =
  | Lvl of int
  | Var of {name : Name.t; twin : Tm.twin; ushift : int}
  | Meta of {name : Name.t; ushift : int}
  | NCoe of {r : dim; r' : dim; ty : neu abs; cap : value}
  | NCom of {r : dim; r' : dim; ty : neu abs; cap : value; sys : con abs sys}

and frame =
  | FunApp of value
  | Fst
  | Snd
  | ExtApp of dim list
  | NHCom of {r : dim; r' : dim; cap : value; sys : con abs sys}
  | VProj of {r : dim; func : value}

and neu =
  {head : head;
   frames : frame bwd}

and cell =
  | Val of con Lazy.t Delayed.t
  | Dim of dim

and env = {globals : GlobalEnv.t; cells : cell bwd}

and clo = Clo of {bnd : Tm.tm Tm.bnd; env : env}
and nclo = NClo of {bnd : Tm.tm Tm.nbnd; env : env}
and ext_clo = ExtClo of {bnd : (Tm.tm * (Tm.tm, Tm.tm) Tm.system) Tm.nbnd; env : env}


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

  (** [plug] applies a stack frame to an element of the domain.

      the invariant is that the frame and the plugee are all rel-rigid. *)
  val plug : rel -> frame -> t -> t
end

module type DelayedDomainPlug =
sig
  (** type t is intended to be the delayed version of type u *)
  type u
  include DomainPlug

  (** create a delayed run *)
  val make : u -> t

  (** force the run created by [make] *)
  val unleash : t -> u

  (** cancel the run (drop the held rel). the caller has the
      responsibility to apply proper restrictions. *)
  val drop_rel : t -> u

  (** some convenience function that might be more optimized *)

  (** run_then_unleash rel x = unleash (run rel x) *)
  val run_then_unleash : rel -> t -> u

  (** plug_then_unleash rel frm x = unleash (plug rel frm x) *)
  val plug_then_unleash : rel -> frame -> t -> u
end

module rec Syn :
sig
  type t = Tm.tm
  exception Triv of con
  (* invariant: everything in env should already be rel-value *)
  val eval : rel -> env -> t -> con
  val eval_dim : env -> t -> dim
  val eval_tm_sys : rel -> env -> (t, t) Tm.system -> con sys
end =
struct
  type t = Tm.tm

  exception Triv of con

  module LazyVal = DelayedPlug (LazyPlug (Con))
  module LazyValAbs = DelayedPlug (LazyPlug (AbsPlug (Con)))

  let rec eval_dim env t =
    match Tm.unleash t with
    | Tm.Dim0 -> `Dim0
    | Tm.Dim1 -> `Dim1
    | Tm.Up (Tm.Ix (i, _), []) ->
      begin
        match Env.lookup_cell_by_index i env with
        | Dim r -> r
        | _ -> raise PleaseRaiseProperError
      end
    | Tm.Up (Tm.Var {name; _}, []) -> `Atom name
    | Tm.Up (Tm.DownX r, []) -> eval_dim env r
    | _ -> raise PleaseRaiseProperError

  let rec eval rel env t =
    match Tm.unleash t with
    | Tm.Up cmd ->
      eval_cmd rel env cmd

    | Tm.Let (c, Tm.B (_, t)) ->
      let v = lazy begin eval_cmd rel env c end in
      eval rel (Env.extend_cell env @@ Val (LazyVal.make v)) t

    | Tm.Pi (dom, cod) ->
      let dom = Val.make @@ eval rel env dom in
      let cod = Clo {bnd = cod; env} in
      Pi {dom; cod}
    | Tm.Lam bnd ->
      Lam (Clo {bnd; env})

    | Tm.Sg (dom, cod) ->
      let dom = Val.make @@ eval rel env dom in
      let cod = Clo {bnd = cod; env} in
      Sg {dom; cod}
    | Tm.Cons (t0, t1) ->
      let v0 = Val.make @@ eval rel env t0 in
      let v1 = Val.make @@ eval rel env t1 in
      Cons (v0, v1)

    | Tm.Ext bnd ->
      Ext (ExtClo {bnd; env})
    | Tm.ExtLam bnd ->
      ExtLam (NClo {bnd; env})
    | Tm.Dim0 | Tm.Dim1 ->
      raise PleaseRaiseProperError

    | Tm.Restrict _ ->
      raise PleaseFillIn
    | Tm.RestrictThunk _ ->
      raise PleaseFillIn

    | Tm.Univ {kind; lvl} ->
      Univ {kind; lvl}

    | Tm.V _ ->
      raise PleaseFillIn
    | Tm.VIn _ ->
      raise PleaseFillIn

    | Tm.FHCom info ->
      let r = eval_dim env info.r in
      let r' = eval_dim env info.r' in
      let cap = Val.make @@ eval rel env info.cap in
      let sys = eval_bnd_sys rel env info.sys in
      Con.make_fhcom rel r r' ~cap ~sys
    | Tm.Box _ ->
      raise PleaseFillIn

    | Tm.LblTy _ ->
      raise PleaseFillIn
    | Tm.LblRet _ ->
      raise PleaseFillIn

    | Tm.Later _ ->
      raise CanJonHelpMe
    | Tm.Next _ ->
      raise CanJonHelpMe

    | Tm.Data _ ->
      raise CanJonHelpMe
    | Tm.Intro _ ->
      raise CanJonHelpMe

  and eval_cmd rel env (hd, sp) =
    let folder hd frm =
      let frm = eval_frame rel env frm in
      Con.plug rel frm hd
    in
    List.fold_left folder (eval_head rel env hd) sp

  and eval_frame rel env =
    function
    | Tm.Fst -> Fst
    | Tm.Snd -> Snd
    | Tm.FunApp t -> FunApp (Val.make @@ eval rel env t)
    | Tm.ExtApp l -> ExtApp (List.map (eval_dim env) l)
    | _ -> raise PleaseFillIn

  and eval_bnd rel env =
    function
    | Tm.B (nm, tm) ->
      let x = Name.named nm in
      let env = Env.extend_cell env @@ Dim (`Atom x) in
      Abs (x, eval rel env tm)

  and eval_head rel env =
    function
    | Tm.Down info ->
      eval rel env info.tm

    | Tm.DownX _ -> raise PleaseRaiseProperError

    | Tm.HCom info ->
      let r = eval_dim env info.r in
      let r' = eval_dim env info.r' in
      let ty = eval rel env info.ty in
      let cap = Val.make @@ eval rel env info.cap in
      let sys = eval_bnd_sys rel env info.sys in
      Con.make_hcom rel r r' ~ty ~cap ~sys

    | Tm.Coe info ->
      let r = eval_dim env info.r in
      let r' = eval_dim env info.r' in
      let abs = eval_bnd rel env info.ty  in
      let cap = Val.make @@ eval rel env info.tm in
      Con.make_coe rel r r' ~abs ~cap

    | Tm.Com info ->
      let r = eval_dim env info.r in
      let r' = eval_dim env info.r' in
      let abs = eval_bnd rel env info.ty in
      let cap = Val.make @@ eval rel env info.cap in
      let sys = eval_bnd_sys rel env info.sys in
      Con.make_com rel r r' ~abs ~cap ~sys

    | Tm.GHCom _ -> raise PleaseFillIn
    | Tm.GCom _ -> raise PleaseFillIn

    | Tm.Ix (i, _) ->
      begin
        match Env.lookup_cell_by_index i env with
        | Val v -> Lazy.force @@ LazyVal.unleash v
        | _ -> raise PleaseRaiseProperError
      end

    | Tm.Var info ->
      let globals = env.globals in
      let entry = GlobalEnv.lookup globals info.name in
      let env' = Env.clear_locals env in
      let ty, odef =
        match entry, info.twin with
        | `Def (ty, def), _ -> ty, Some def
        | `P ty, _ -> ty, None
        | `Tw (ty, _), `TwinL -> ty, None
        | `Tw (_, ty), `TwinR -> ty, None
        | _ -> raise PleaseRaiseProperError
      in
      begin
        match odef with
        | Some def ->
          eval rel env' @@ Tm.shift_univ info.ushift def
        | None ->
          let vty = eval rel env' @@ Tm.shift_univ info.ushift ty in
          let var = Var {name = info.name; twin = info.twin; ushift = info.ushift} in
          let neu = {head = var; frames = Emp} in
          Neu {neu; ty = Delayed.make vty; sys = []}
      end

    | Tm.Meta info ->
      let globals = env.globals in
      let entry = GlobalEnv.lookup globals info.name in
      let env' = Env.clear_locals env in
      let ty, odef =
        match entry with
        | `Def (ty, def) -> ty, Some def
        | `P ty -> ty, None
        | _ -> raise PleaseRaiseProperError
      in
      begin
        match odef with
        | Some def ->
          eval rel env' @@ Tm.shift_univ info.ushift def
        | None ->
          let vty = eval rel env' @@ Tm.shift_univ info.ushift ty in
          let var = Meta {name = info.name; ushift = info.ushift} in
          let neu = {head = var; frames = Emp} in
          Neu {neu; ty = Delayed.make vty; sys = []}
      end

    | Tm.DFix _ -> raise CanJonHelpMe

  and eval_bnd_face rel env (tr, tr', bnd_opt) =
    match bnd_opt with
    | Some bnd ->
      let r = eval_dim env tr in
      let r' = eval_dim env tr' in
      let abs = lazy begin eval_bnd rel env bnd end in
      (r, r', LazyValAbs.make abs)
    | None -> raise PleaseRaiseProperError

  and eval_bnd_sys rel env =
    List.map (eval_bnd_face rel env)

  and eval_tm_face rel env (tr, tr', tm_opt) =
    match tm_opt with
    | Some tm ->
      let r = eval_dim env tr in
      let r' = eval_dim env tr' in
      let v = lazy begin eval rel env tm end in
      (r, r', LazyVal.make v)
    | None -> raise PleaseRaiseProperError

  and eval_tm_sys rel env =
    List.map (eval_tm_face rel env)
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

  let swap pi (Clo clo) =
    Clo {clo with env = Env.swap pi clo.env}
  let subst r x (Clo clo) =
    Clo {clo with env = Env.subst r x clo.env}
  let run rel (Clo clo) =
    Clo {clo with env = Env.run rel clo.env}
  let subst_then_run rel r x (Clo clo) =
    Clo {clo with env = Env.subst_then_run rel r x clo.env}

  let inst rel clo cell =
    let Clo {bnd; env} = clo in
    let Tm.B (_, tm) = bnd in
    Syn.eval rel (Env.extend_cell env cell) tm
end

and NClo :
sig
  include Domain with type t = nclo
  val inst : rel -> t -> cell list -> con
end =
struct
  type t = nclo

  let swap pi (NClo nclo) =
    NClo {nclo with env = Env.swap pi nclo.env}
  let subst r x (NClo nclo) =
    NClo {nclo with env = Env.subst r x nclo.env}
  let run rel (NClo nclo) =
    NClo {nclo with env = Env.run rel nclo.env}
  let subst_then_run rel r x (NClo nclo) =
    NClo {nclo with env = Env.subst_then_run rel r x nclo.env}

  let inst (rel : rel) nclo cells : con =
    let NClo {bnd; env} = nclo in
    let Tm.NB (_, tm) = bnd in
    Syn.eval rel (Env.extend_cells env cells) tm
end

and ExtClo :
sig
  include Domain with type t = ext_clo
  val inst : rel -> t -> cell list -> con * con sys
end =
struct
  type t = ext_clo

  let swap pi (ExtClo clo) =
    ExtClo {clo with env = Env.swap pi clo.env}
  let subst r x (ExtClo clo) =
    ExtClo {clo with env = Env.subst r x clo.env}
  let run rel (ExtClo clo) =
    ExtClo {clo with env = Env.run rel clo.env}
  let subst_then_run rel r x (ExtClo clo) =
    ExtClo {clo with env = Env.subst_then_run rel r x clo.env}

  let inst rel clo cells =
    let ExtClo {bnd; env} = clo in
    let Tm.NB (_, (ty, sys)) = bnd in
    let env' = Env.extend_cells env cells in
    let vty = Syn.eval rel env' ty in
    let vsys = Syn.eval_tm_sys rel env' sys in
    vty, vsys
end

and Cell : Domain with type t = cell =
struct
  type t = cell

  module LazyValue = DelayedPlug (LazyPlug (Con))

  let swap pi =
    function
    | Dim d -> Dim (Dim.swap pi d)
    | Val v -> Val (LazyValue.swap pi v)
  let subst r x =
    function
    | Dim d -> Dim (Dim.subst r x d)
    | Val v -> Val (LazyValue.subst r x v)
  let run rel =
    function
    | Dim _ as c -> c
    | Val v -> Val (LazyValue.run rel v)
  let subst_then_run rel r x =
    function
    | Dim d -> Dim (Dim.subst_then_run rel r x d)
    | Val v -> Val (LazyValue.subst_then_run rel r x v)
end

and Env :
sig
  include Domain with type t = env

  val init : GlobalEnv.t -> env (* shouldn't this take a GlobalEnv.t? *)
  val extend_cell : env -> cell -> env
  val extend_cells : env -> cell list -> env
  val lookup_cell_by_index : int -> env -> cell

  val clear_locals : env -> env
end =
struct
  type t = env

  module LazyValue = DelayedPlug (LazyPlug (Con))

  let swap pi env =
    {env with cells = Bwd.map (Cell.swap pi) env.cells}
  let subst r x env =
    {env with cells = Bwd.map (Cell.subst r x) env.cells}
  let run rel env =
    {env with cells = Bwd.map (Cell.run rel) env.cells}
  let subst_then_run rel r x env =
    {env with cells = Bwd.map (Cell.subst_then_run rel r x) env.cells}

  let init globals = {globals = globals; cells = Emp}

  let lookup_cell_by_index i {cells; _} = Bwd.nth cells i

  let extend_cells env cells =
    {env with cells = env.cells <>< cells}

  let extend_cell env cell =
    extend_cells env [cell]

  let clear_locals env =
    {globals = env.globals; cells = Emp}
end

and Con :
sig
  include DomainPlug with type t = con

  (** invariant: abs and cap are rel-values, but dir might not be rigid *)
  val make_coe : rel -> dim -> dim -> abs:con abs -> cap:value -> con

  (** invariant: ty, cap and sys are rel-values, but dir and sys might not be rigid *)
  val make_hcom : rel -> dim -> dim -> ty:con -> cap:value -> sys:con abs sys -> con

  (** invariant: abs, cap and sys are rel-values, but dir and sys might not be rigid *)
  val make_com : rel -> dim -> dim -> abs:con abs -> cap:value -> sys:con abs sys -> con

  (** invariant: cap and sys are rel-values, but dir and sys might not be rigid *)
  val make_fhcom : rel -> dim -> dim -> cap:value -> sys:con abs sys -> con

  (** invariant: ty1 is a rel-value, ty0 and equiv give {rel,r=0}-values, but r:dim might not be rigid *)
  val make_v : rel -> dim -> ty0:(rel -> value) -> ty1:value -> equiv:(rel -> value) -> con

  (** invariant: el1 is a rel-value, el0 gives a {rel,r=0}-value, but r:dim might not be rigid *)
  val make_vin : rel -> dim -> el0:(rel -> value) -> el1:value -> con
end =
struct
  module ConAbs = AbsPlug (Con)
  module ConSys = Sys (Con)
  module ConFace = Face (Con)
  module ConAbsFace = Face (AbsPlug (Con))
  module ConAbsSys = Sys (AbsPlug (Con))
  module ValAbs = DelayedAbsPlug (Con)
  module LazyVal = DelayedPlug (LazyPlug (Con))

  type t = con

  let swap pi =
    function
    | Pi quant ->
      let quant = Quantifier.swap pi quant in
      Pi quant

    | Sg quant ->
      let quant = Quantifier.swap pi quant in
      Sg quant

    | Ext extclo ->
      let extclo = ExtClo.swap pi extclo in
      Ext extclo

    | Lam clo ->
      let clo = Clo.swap pi clo in
      Lam clo

    | Cons (v0, v1) ->
      let v0 = Val.swap pi v0 in
      let v1 = Val.swap pi v1 in
      Cons (v0, v1)

    | ExtLam nclo ->
      let nclo = NClo.swap pi nclo in
      ExtLam nclo

    | Coe info ->
      Coe
        {r = Dim.swap pi info.r;
         r' = Dim.swap pi info.r';
         ty = CoeShape.swap pi info.ty;
         cap = Val.swap pi info.cap}

    | HCom info ->
      HCom
        {r = Dim.swap pi info.r;
         r' = Dim.swap pi info.r';
         ty = HComShape.swap pi info.ty;
         cap = Val.swap pi info.cap;
         sys = ConAbsSys.swap pi info.sys}

    | Com info ->
      Com
        {r = Dim.swap pi info.r;
         r' = Dim.swap pi info.r';
         ty = ComShape.swap pi info.ty;
         cap = Val.swap pi info.cap;
         sys = ConAbsSys.swap pi info.sys}

    | Univ _ as con -> con

    | V {r; ty0; ty1; equiv} ->
      V
        {r = Dim.swap pi r;
         ty0 = Val.swap pi ty0;
         ty1 = Val.swap pi ty1;
         equiv = Val.swap pi equiv}

    | VIn {r; el0; el1} ->
      VIn
        {r = Dim.swap pi r;
         el0 = Val.swap pi el0;
         el1 = Val.swap pi el1}

    | Neu info ->
      Neu
        {ty = Val.swap pi info.ty;
         neu = Neu.swap pi info.neu;
         sys = ConSys.swap pi info.sys}

  let subst r x =
    function
    | Pi quant ->
      let quant = Quantifier.subst r x quant in
      Pi quant

    | Sg quant ->
      let quant = Quantifier.subst r x quant in
      Sg quant

    | Ext extclo ->
      let extclo = ExtClo.subst r x extclo in
      Ext extclo

    | Lam clo ->
      let clo = Clo.subst r x clo in
      Lam clo

    | Cons (v0, v1) ->
      let v0 = Val.subst r x v0 in
      let v1 = Val.subst r x v1 in
      Cons (v0, v1)

    | ExtLam nclo ->
      let nclo = NClo.subst r x nclo in
      ExtLam nclo

    | Coe info ->
      Coe
        {r = Dim.subst r x info.r;
         r' = Dim.subst r x info.r';
         ty = CoeShape.subst r x info.ty;
         cap = Val.subst r x info.cap}

    | HCom info ->
      HCom
        {r = Dim.subst r x info.r;
         r' = Dim.subst r x info.r';
         ty = HComShape.subst r x info.ty;
         cap = Val.subst r x info.cap;
         sys = ConAbsSys.subst r x info.sys}

    | Com info ->
      Com
        {r = Dim.subst r x info.r;
         r' = Dim.subst r x info.r';
         ty = ComShape.subst r x info.ty;
         cap = Val.subst r x info.cap;
         sys = ConAbsSys.subst r x info.sys}

    | Univ _ as con -> con

    | V info ->
      V
        {r = Dim.subst r x info.r;
         ty0 = Val.subst r x info.ty0;
         ty1 = Val.subst r x info.ty1;
         equiv = Val.subst r x info.equiv}

    | VIn info ->
      VIn
        {r = Dim.subst r x info.r;
         el0 = Val.subst r x info.el0;
         el1 = Val.subst r x info.el1}

    | Neu info ->
      Neu
        {ty = Val.subst r x info.ty;
         neu = Neu.subst r x info.neu;
         sys = ConSys.subst r x info.sys}

  let rec run rel =
    function
    | Pi quant ->
      let quant = Quantifier.run rel quant in
      Pi quant

    | Sg quant ->
      let quant = Quantifier.run rel quant in
      Sg quant

    | Ext extclo ->
      let extclo = ExtClo.run rel extclo in
      Ext extclo

    | Lam clo ->
      let clo = Clo.run rel clo in
      Lam clo

    | Cons (v0, v1) ->
      let v0 = Val.run rel v0 in
      let v1 = Val.run rel v1 in
      Cons (v0, v1)

    | ExtLam nclo ->
      let nclo = NClo.run rel nclo in
      ExtLam nclo

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
          match ConAbsSys.run_then_force rel info.sys with
          | sys ->
            let cap = Val.run rel info.cap in
            let ty = HComShape.run rel info.ty in
            HCom {info with ty; cap; sys}

          | exception ConAbsSys.Triv abs ->
            ConAbs.inst rel abs info.r'
      end

    | Com info ->
      begin
        match Rel.compare info.r info.r' rel with
        | `Same ->
          Val.run_then_unleash rel info.cap
        | _ ->
          match ConAbsSys.run_then_force rel info.sys with
          | sys ->
            let cap = Val.run rel info.cap in
            let ty = ComShape.run rel info.ty in
            Com {info with ty; cap; sys}

          | exception ConAbsSys.Triv abs ->
            ConAbs.inst rel abs info.r'
      end

    | Univ _ as con -> con

    | V {r; ty0; ty1; equiv} ->
      let ty0 rel0 = Val.run rel0 ty0 in
      let ty1 = Val.run rel ty1 in
      let equiv rel0 = Val.run rel0 equiv in
      make_v rel r ~ty0 ~ty1 ~equiv

    | VIn {r; el0; el1} ->
      let el0 rel0 = Val.run rel0 el0 in
      let el1 = Val.run rel el1 in
      make_vin rel r ~el0 ~el1

    | Neu info ->
      begin
        match ConSys.run_then_force rel info.sys with
        | sys ->
          let neu = Neu.run rel info.neu in
          let ty = Val.run rel info.ty in
          Neu {ty; neu; sys}
        | exception ConSys.Triv v ->
          v
      end


  and plug rel frm hd =
    match frm, hd with
    | FunApp arg, Lam clo ->
      Clo.inst rel clo @@ Val (LazyVal.make @@ lazy begin Val.unleash arg end)

    | FunApp arg, HCom {r; r'; ty = `Pi quant; cap; sys} ->
      let ty = Clo.inst rel quant.cod @@ Val (LazyVal.make @@ lazy begin Val.unleash arg end) in
      let cap = Val.plug rel frm cap in
      let sys = ConAbsSys.plug rel frm sys in
      rigid_hcom rel r r' ~ty ~cap ~sys

    | FunApp arg, Coe {r; r'; ty = `Pi abs; cap} ->
      let Abs (x, quantx) = abs in
      let y, pi = Perm.freshen_name x in
      let dom = ValAbs.unleash @@ Abs (x, quantx.dom) in
      let coe_arg s = make_coe rel r' s ~abs:dom ~cap:arg in
      let abs =
        let cod_y = Clo.swap pi quantx.cod in
        let coe_r'y = LazyVal.make @@ lazy begin coe_arg @@ `Atom y end in
        Abs (y, Clo.inst rel cod_y @@ Val coe_r'y) in
      let cap = Val.plug rel (FunApp (Val.make @@ coe_arg r)) cap in
      rigid_coe rel r r' ~abs ~cap

    | Fst, Cons (v0, _) ->
      Val.unleash v0

    | Fst, HCom {r; r'; ty = `Sg {dom; _}; cap; sys} ->
      let ty = Val.unleash dom in
      let cap = Val.plug rel Fst cap in
      let sys = ConAbsSys.plug rel Fst sys in
      rigid_hcom rel r r' ~ty ~cap ~sys

    | Fst, Coe {r; r'; ty = `Sg abs; cap} ->
      let cap = Val.plug rel Fst cap in
      let abs =
        let Abs (x, {dom; _}) = abs in
        Abs (x, Val.unleash dom)
      in
      rigid_coe rel r r' ~abs ~cap

    | Snd, Cons (_, v1) ->
      Val.unleash v1

    | Snd, HCom {r; r'; ty = `Sg {dom; cod}; cap; sys} ->
      let abs =
        let y = Name.fresh () in
        let hcom_ry_fst = LazyVal.make @@
          lazy begin
            let ty = Val.unleash dom in
            let cap = Val.plug rel Fst cap in
            let sys = ConAbsSys.plug rel Fst sys in
            rigid_hcom rel r (`Atom y) ~ty ~cap ~sys
          end
        in
        let cod_hcom_ry_fst = Clo.inst rel cod @@ Val hcom_ry_fst in
        Abs (y, cod_hcom_ry_fst)
      in
      let cap = Val.plug rel Snd cap in
      let sys = ConAbsSys.plug rel Snd sys in
      rigid_com rel r r' ~abs ~cap ~sys

    | Snd, Coe {r; r'; ty = `Sg (Abs (x, {dom = dom_x; cod = cod_x})); cap} ->
      let abs =
        let y, pi = Perm.freshen_name x in
        let coe_ry_fst = LazyVal.make @@
          lazy begin
            let abs = ValAbs.unleash @@ Abs (x, dom_x) in
            let cap = Val.plug rel Fst cap in
            rigid_coe rel r (`Atom y) ~abs ~cap
          end
        in
        let cod_y = Clo.swap pi cod_x in
        let cod_y_coe_ry_fst = Clo.inst rel cod_y @@ Val coe_ry_fst in
        Abs (y, cod_y_coe_ry_fst)
      in
      let cap = Val.plug rel Snd cap in
      rigid_coe rel r r' ~abs ~cap

    | ExtApp rs, ExtLam nclo ->
      NClo.inst rel nclo @@ List.map (fun r -> Dim r) rs

    | ExtApp rs as frm, HCom {r; r'; ty = `Ext extclo; cap; sys} ->
      let ty, ext_sys =
        let dim_cells = List.map (fun x -> Dim x) rs in
        ExtClo.inst rel extclo dim_cells
      in
      begin
        match ConSys.force rel ext_sys with
        | ext_sys ->
          let cap = Val.plug rel frm cap in
          let ext_sys = ConAbsSys.foreach_gen ext_sys @@
            fun (r, r', bdy) ->
            let x = Name.fresh () in
            Abs (x, Lazy.force bdy)
          in
          let comp_sys = ConAbsSys.plug rel frm sys in
          let sys = ext_sys @ comp_sys in
          rigid_hcom rel r r' ~ty ~cap ~sys
        | exception ConSys.Triv c -> c
      end

    | ExtApp rs as frm, Coe {r; r'; ty = `Ext (Abs (x, extclo_x)); cap} ->
      let y, rel_y, extclo_y =
        match Frame.occur1 x frm with
        | `No ->
          x, Rel.hide' x rel, extclo_x
        | `Might ->
          let y, pi = Perm.freshen_name x in
          let extclo_y = ExtClo.swap pi extclo_x in
          y, rel, extclo_y
      in
      let ty_y, sys_y =
        let dim_cells = List.map (fun x -> Dim x) rs in
        ExtClo.inst rel_y extclo_y dim_cells
      in
      begin
        match ConSys.force rel sys_y with
        | sys_y ->
          let abs = Abs (y, ty_y) in
          let cap = Val.plug rel frm cap in
          let sys = ConAbsSys.foreach_gen sys_y @@
            fun (r, r', bdy_y) -> Abs (y, Lazy.force bdy_y)
          in
          rigid_com rel r r' ~abs ~cap ~sys
        | exception ConSys.Triv c_y ->
          subst_then_run rel r' y c_y
      end

    | NHCom {r; r'; cap; sys}, con ->
      rigid_hcom rel r r' ~ty:con ~cap ~sys

    | VProj {r; func}, con ->
      rigid_vproj rel r ~el:con ~func

    | (FunApp _ | Fst | Snd | ExtApp _), Neu info ->
      let neu = Neu.plug rel frm info.neu in
      let sys = ConSys.plug rel frm info.sys in
      let ty, sys' = plug_ty rel frm info.ty hd in
      Neu {ty = Val.make ty; neu; sys = sys' @ sys}

    | FunApp _, _ -> raise PleaseRaiseProperError
    | Fst, _ -> raise PleaseRaiseProperError
    | Snd, _ -> raise PleaseRaiseProperError
    | ExtApp _, _ -> raise PleaseRaiseProperError

  and plug_ty rel frm ty hd =
    match Val.unleash ty, frm with
    | Pi {dom; cod}, FunApp arg ->
      let arg = lazy begin Val.unleash arg end in
      Clo.inst rel cod @@ Val (LazyVal.make arg), []

    | Pi _, _ -> raise PleaseRaiseProperError

    | Sg {dom; _}, Fst ->
      Val.unleash dom, []

    | Sg {cod; _}, Snd ->
      let fst = LazyVal.make @@ lazy begin plug rel Fst hd end in
      Clo.inst rel cod @@ Val fst, []

    | Sg _, _ -> raise PleaseRaiseProperError

    | Ext extclo, ExtApp rs ->
      ExtClo.inst rel extclo @@ List.map (fun r -> Dim r) rs

    | Ext _, _ -> raise PleaseRaiseProperError

    | HCom {ty = `Pos; _}, _ -> raise PleaseFillIn

    | _ ->
      raise PleaseRaiseProperError

  and make_coe rel r r' ~abs ~cap =
    match Rel.compare r r' rel with
    | `Same ->
      Val.unleash cap
    | _ ->
      rigid_coe rel r r' ~abs ~cap

  and make_hcom rel r r' ~ty ~cap ~sys =
    match Rel.compare r r' rel with
    | `Same ->
      Val.unleash cap
    | _ ->
      match ConAbsSys.run_then_force rel sys with
      | _ ->
        rigid_hcom rel r r' ~ty ~cap ~sys
      | exception ConAbsSys.Triv abs ->
        ConAbs.inst rel abs r'

  and make_com rel r r' ~abs ~cap ~sys =
    match Rel.compare r r' rel with
    | `Same ->
      Val.unleash cap
    | _ ->
      match ConAbsSys.force rel sys with
      | _ ->
        rigid_com rel r r' ~abs ~cap ~sys
      | exception ConAbsSys.Triv abs ->
        ConAbs.inst rel abs r'

  and make_fhcom rel r r' ~cap ~sys =
    match Rel.compare r r' rel with
    | `Same ->
      Val.unleash cap
    | _ ->
      match ConAbsSys.run_then_force rel sys with
      | _ ->
        HCom {r; r'; ty = `Pos; cap; sys}
      | exception ConAbsSys.Triv abs ->
        ConAbs.inst rel abs r'

  and make_v rel r ~ty0 ~ty1 ~equiv =
    match Rel.equate r `Dim0 rel with
    | `Same -> Val.unleash @@ ty0 rel
    | exception I.Inconsistent -> Val.unleash ty1
    | `Changed rel0 ->
      V {r; ty0 = ty0 rel0; ty1; equiv = equiv rel0}

  and make_vin rel r ~el0 ~el1 =
    match Rel.equate r `Dim0 rel with
    | `Same -> Val.unleash @@ el0 rel
    | exception I.Inconsistent -> Val.unleash el1
    | `Changed rel0 ->
      VIn {r; el0 = el0 rel0; el1}

  and make_vproj rel r ~el ~func =
    match Rel.compare r `Dim0 rel with
    | `Same -> Val.plug_then_unleash rel (FunApp (Val.make el)) func
    | `Apart -> el
    | `Indet -> rigid_vproj rel r ~el ~func

  and rigid_hcom rel r r' ~ty ~cap ~sys =
    match ty with
    | Sg quant ->
      HCom {r; r'; ty = `Sg quant; cap; sys}

    | Pi quant ->
      HCom {r; r'; ty = `Pi quant; cap; sys}

    | Ext extclo ->
      HCom {r; r'; ty = `Ext extclo; cap; sys}

    | Univ _ ->
      HCom {r; r'; ty = `Pos; cap; sys}

    | HCom {ty = `Pos; _} ->
      raise CanFavoniaHelpMe

    | Neu info ->
      let nhcom = NHCom {r; r'; cap; sys} in
      let neu = {info.neu with frames = info.neu.frames #< nhcom} in
      let neu_sys =
        let cap_face = r, r', LazyVal.make @@ lazy begin Val.unleash cap end in
        let tube_faces =
          ConSys.foreach_gen sys @@ fun (s, s', abs) ->
          let rel' = Rel.equate' s s' rel in
          ConAbs.inst rel' (Lazy.force abs) r'
        in
        let old_faces =
          ConSys.foreach_gen info.sys @@ fun (s, s', ty) ->
          let rel' = Rel.equate' s s' rel in
          let ty = run rel' @@ Lazy.force ty in
          let cap = Val.run rel' cap in
          let sys = ConAbsSys.run rel' sys in
          make_hcom rel' r r' ~ty ~cap ~sys
        in
        cap_face :: tube_faces @ old_faces
      in
      Neu {ty = Val.make ty; neu; sys = neu_sys}

    | _ ->
      raise PleaseRaiseProperError

  (** Invariant: everything is already a value wrt. [rel], and it [r~>r'] is [rel]-rigid. *)
  and rigid_coe rel r r' ~abs ~cap : con =
    let Abs (x, tyx) = abs in
    match tyx with
    | Sg quant ->
      Coe {r; r'; ty = `Sg (Abs (x, quant)); cap}

    | Pi quant ->
      Coe {r; r'; ty = `Pi (Abs (x, quant)); cap}

    | Ext extclo ->
      Coe {r; r'; ty = `Ext (Abs (x, extclo)); cap}

    | Univ _ ->
      Val.unleash cap

    | HCom {ty = `Pos; _} ->
      raise CanFavoniaHelpMe

    | V _ ->
      raise CanFavoniaHelpMe

    | Neu info ->
      let neu = {head = NCoe {r; r'; ty = Abs (x, info.neu); cap}; frames = Emp} in
      let ty = ValAbs.inst rel (ValAbs.make abs) r' in
      let sys =
        let cap_face = r, r', LazyVal.make @@ lazy begin Val.unleash cap end in
        let old_faces =
          ConSys.forall_then_foreach x info.sys @@ ConFace.gen @@ fun (s, s', bdy) ->
          let rel' = Rel.equate' s s' rel in
          let abs = ConAbs.run rel' @@ Abs (x, Lazy.force bdy) in
          let cap = Val.run rel' cap in
          make_coe rel' r r' ~abs ~cap
        in
        cap_face :: old_faces
      in
      Neu {ty; neu; sys}

    | _ ->
      raise PleaseRaiseProperError

  and expand_rigid_com rel r r' ~abs ~cap ~sys =
    let ty = ConAbs.inst rel abs r' in
    let cap = Val.make @@ make_coe rel r' r ~abs ~cap in
    let sys =
      let Abs (bound_var_of_abs, _) = abs in
      ConAbsSys.foreach_gen sys @@ fun (r, r', face) ->
      let rel' = Rel.equate r r' in
      let Abs (y, bdy_y) = Lazy.force face in
      let z, rel_z, bdy_z =
        (* it might sound weird that y could be the same as bound_var_of_abs,
         * but this happens a lot in the coe of the extension types. *)
        if y = bound_var_of_abs && I.absent y r' then
          y, Rel.hide' y rel, bdy_y
        else
          let z, pi = Perm.freshen_name y in
          z, rel, Con.swap pi bdy_y
      in
      Abs (z, make_coe rel_z r' (`Atom z) ~abs ~cap:(Val.make bdy_z))
    in
    rigid_hcom rel r r' ~ty ~cap ~sys

  and rigid_com rel r r' ~abs ~cap ~sys =
    let Abs (x, tyx) = abs in
    match tyx with
    | Sg quant ->
      Com {r; r'; ty = `Sg (Abs (x, quant)); cap; sys}

    | Pi quant ->
      Com {r; r'; ty = `Pi (Abs (x, quant)); cap; sys}

    | Ext extclo ->
      Com {r; r'; ty = `Ext (Abs (x, extclo)); cap; sys}

    | Neu info ->
      let neu = {head = NCom {r; r'; ty = Abs (x, info.neu); cap; sys}; frames = Emp} in
      let ty = ValAbs.inst rel (ValAbs.make abs) r' in
      let neu_sys =
        let cap_face = r, r', LazyVal.make @@ lazy begin Val.unleash cap end in
        let tube_faces =
          ConSys.foreach_gen sys @@ fun (s, s', abs) ->
          let rel' = Rel.equate' s s' rel in
          ConAbs.inst rel' (Lazy.force abs) r'
        in
        let old_faces =
          ConSys.forall_then_foreach x info.sys @@ ConFace.gen @@ fun (s, s', bdy) ->
          let rel' = Rel.equate' s s' rel in
          let abs = ConAbs.run rel' @@ Abs (x, Lazy.force bdy) in
          let cap = Val.run rel' cap in
          let sys = ConAbsSys.run rel' sys in
          make_com rel' r r' ~abs ~cap ~sys
        in
        cap_face :: tube_faces @ old_faces
      in
      Neu {ty; neu; sys = neu_sys}

    | Univ _ as ty -> rigid_hcom rel r r' ~ty ~cap ~sys

    | HCom {ty = `Pos; _} -> expand_rigid_com rel r r' ~abs ~cap ~sys

    | V _ ->
      raise CanFavoniaHelpMe

    | _ ->
      raise PleaseRaiseProperError

  and rigid_vproj rel r ~el ~func =
    match el with
    | VIn {el1; _} ->
      Val.unleash el1

    | Neu _ ->
      raise PleaseFillIn

    | _ ->
      raise PleaseRaiseProperError

  and subst_then_run rel r x c =
    run rel @@ subst r x c
end

and Val : DelayedDomainPlug
  with type u = con
   and type t = con Delayed.t
  = DelayedPlug (Con)

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

and ComShape : Domain with type t = com_shape = CoeShape

and Quantifier : Domain with type t = quantifier =
struct
  type t = quantifier

  let swap pi {dom; cod} =
    let dom = Val.swap pi dom in
    let cod = Clo.swap pi cod in
    {dom; cod}
  let subst r x {dom; cod} =
    let dom = Val.subst r x dom in
    let cod = Clo.subst r x cod in
    {dom; cod}
  let run rel {dom; cod} =
    let dom = Val.run rel dom in
    let cod = Clo.run rel cod in
    {dom; cod}
  let subst_then_run rel r x {dom; cod} =
    let dom = Val.subst_then_run rel r x dom in
    let cod = Clo.subst_then_run rel r x cod in
    {dom; cod}
end

and Neu : DomainPlug with type t = neu =
struct
  type t = neu

  let swap pi neu =
    {head = Head.swap pi neu.head;
     frames = Bwd.map (Frame.swap pi) neu.frames}
  let run rel neu =
    {head = Head.run rel neu.head;
     frames = Bwd.map (Frame.run rel) neu.frames}
  let subst r x neu =
    {head = Head.subst r x neu.head;
     frames = Bwd.map (Frame.subst r x) neu.frames}
  let subst_then_run rel r x neu =
    {head = Head.subst_then_run rel r x neu.head;
     frames = Bwd.map (Frame.subst_then_run rel r x) neu.frames}

  let plug rel frm neu =
    {neu with
     frames = neu.frames #< frm}
end

and Head : Domain with type t = head =
struct
  type t = head

  module NeuAbs = Abs (Neu)
  module ConAbsSys = Sys (AbsPlug (Con))

  let swap pi =
    function
    | Lvl _ | Var _ | Meta _ as h -> h
    | NCoe info ->
      NCoe
        {r = Dim.swap pi info.r;
         r' = Dim.swap pi info.r';
         ty = NeuAbs.swap pi info.ty;
         cap = Val.swap pi info.cap}
    | NCom info ->
      NCom
        {r = Dim.swap pi info.r;
         r' = Dim.swap pi info.r';
         ty = NeuAbs.swap pi info.ty;
         cap = Val.swap pi info.cap;
         sys = ConAbsSys.swap pi info.sys}

  let run rel =
    function
    | Lvl _ | Var _ | Meta _ as h -> h
    | NCoe info ->
      NCoe
        {r = Dim.run rel info.r;
         r' = Dim.run rel info.r';
         ty = NeuAbs.run rel info.ty;
         cap = Val.run rel info.cap}
    | NCom info ->
      NCom
        {r = Dim.run rel info.r;
         r' = Dim.run rel info.r';
         ty = NeuAbs.run rel info.ty;
         cap = Val.run rel info.cap;
         sys = ConAbsSys.run rel info.sys}

  let subst r x =
    function
    | Lvl _ | Var _ | Meta _ as h -> h
    | NCoe info ->
      NCoe
        {r = Dim.subst r x info.r;
         r' = Dim.subst r x info.r';
         ty = NeuAbs.subst r x info.ty;
         cap = Val.subst r x info.cap}
    | NCom info ->
      NCom
        {r = Dim.subst r x info.r;
         r' = Dim.subst r x info.r';
         ty = NeuAbs.subst r x info.ty;
         cap = Val.subst r x info.cap;
         sys = ConAbsSys.subst r x info.sys}

  let subst_then_run rel r x =
    function
    | Lvl _ | Var _ | Meta _ as h -> h
    | NCoe info ->
      NCoe
        {r = Dim.subst_then_run rel r x info.r;
         r' = Dim.subst_then_run rel r x info.r';
         ty = NeuAbs.subst_then_run rel r x info.ty;
         cap = Val.subst_then_run rel r x info.cap}
    | NCom info ->
      NCom
        {r = Dim.subst_then_run rel r x info.r;
         r' = Dim.subst_then_run rel r x info.r';
         ty = NeuAbs.subst_then_run rel r x info.ty;
         cap = Val.subst_then_run rel r x info.cap;
         sys = ConAbsSys.subst_then_run rel r x info.sys}
end

and Frame :
sig
  include Domain with type t = frame
  val occur1 : Name.t -> frame -> [`No | `Might]
  val occur : Name.t bwd -> frame -> [`No | `Might]
end =
struct
  type t = frame

  module ConAbsSys = Sys (AbsPlug (Con))

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
    | NHCom info ->
      NHCom
        {r = Dim.swap pi info.r;
         r' = Dim.swap pi info.r';
         cap = Val.swap pi info.cap;
         sys = ConAbsSys.swap pi info.sys}
    | VProj info ->
      VProj
        {r = Dim.swap pi info.r;
         func = Val.swap pi info.func}

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
    | NHCom info ->
      NHCom
        {r = Dim.subst r x info.r;
         r' = Dim.subst r x info.r';
         cap = Val.subst r x info.cap;
         sys = ConAbsSys.subst r x info.sys}
    | VProj info ->
      VProj
        {r = Dim.subst r x info.r;
         func = Val.subst r x info.func}

  let run rel =
    function
    | FunApp arg ->
      let arg = Val.run rel arg in
      FunApp arg
    | Fst | Snd | ExtApp _ as frm ->
      frm
    | NHCom info ->
      NHCom
        {r = Dim.run rel info.r;
         r' = Dim.run rel info.r';
         cap = Val.run rel info.cap;
         sys = ConAbsSys.run rel info.sys}
    | VProj info ->
      VProj
        {r = Dim.run rel info.r;
         func = Val.run rel info.func}

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
    | NHCom info ->
      NHCom
        {r = Dim.subst_then_run rel r x info.r;
         r' = Dim.subst_then_run rel r x info.r';
         cap = Val.subst_then_run rel r x info.cap;
         sys = ConAbsSys.subst_then_run rel r x info.sys}
    | VProj info ->
      VProj
        {r = Dim.subst_then_run rel r x info.r;
         func = Val.subst_then_run rel r x info.func}

  let occur xs =
    function
    | FunApp _ | NHCom _ | VProj _ ->
      `Might
    | ExtApp dims ->
      if Bwd.for_all (fun x -> List.for_all (I.absent x) dims) xs then
        `No
      else
        `Might
    | Fst | Snd ->
      `No

  let occur1 x = occur (Emp #< x)
end


and Sys :
  functor (X : DomainPlug) ->
  sig
    include DomainPlug with type t = X.t sys
    exception Triv of X.t

    (** this is to force rigidity of a system *)
    val force : rel -> t -> t

    (** this is to remove all faces depending on a particular variable *)
    val forall : Name.t -> t -> t

    (** some convenience functions which could be more efficient *)

    (** run_then_force rel sys = force (run rel sys) *)
    val run_then_force : rel -> t -> t

    (** forall_then_foreach x sys f = List.foreach (forall x sys) f *)
    val forall_then_foreach : Name.t -> t -> (X.t face -> 'b) -> 'b list

    (** foreach_gen sys f = List.foreach sys (Face.gen f) *)
    val foreach_gen : 'a sys -> (dim * dim * 'a Lazy.t -> X.t) -> t
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
        try Some (Face.run rel face)
        with
        | Face.Dead -> None
      in
      ListUtil.filter_map run_face sys

    let subst_then_run rel r x sys =
      let run_face face =
        try Some (Face.subst_then_run rel r x face)
        with
        | Face.Dead -> None
        | Face.Triv bdy -> raise @@ Triv bdy
      in
      ListUtil.filter_map run_face sys

    let plug rel frm sys =
      List.map (Face.plug rel frm) sys

    let force rel sys =
      let force_face face =
        try Some (Face.force rel face)
        with
        | Face.Dead -> None
        | Face.Triv bdy -> raise @@ Triv bdy
      in
      ListUtil.filter_map force_face sys

    let run_then_force rel sys =
      let run_then_force_face face =
        try Some (Face.run_then_force rel face)
        with
        | Face.Dead -> None
        | Face.Triv bdy -> raise @@ Triv bdy
      in
      ListUtil.filter_map run_then_force_face sys

    let forall_then_foreach x sys f =
      ListUtil.filter_map (fun face -> Option.map f (Face.forall x face)) sys

    let foreach_gen sys f = ListUtil.foreach sys (Face.gen f)
  end

and Face :
  functor (X : DomainPlug) ->
  sig
    include DomainPlug with type t = X.t face

    exception Triv of X.t
    exception Dead

    (** this is to force rigidity of a system *)
    val force : rel -> t -> t

    (** this is to remove all faces depending on a particular variable *)
    val forall : Name.t -> t -> t option

    (* a generator for hooking up `run`, assuming the provided function
     * will then sufficiently restrict the body. the body fed into the externally
     * function might be less restricted then the previous run or the cobifration
     * suggests.
     *
     * Note that this will not force the generated face. *)
    val gen : (dim * dim * 'a Lazy.t -> X.t) -> 'a face -> t

    (** some convenience functions which could be more efficient *)

    (** run_then_force rel face = force (run rel face) *)
    val run_then_force : rel -> t -> t
  end =
  functor (X : DomainPlug) ->
  struct
    module DelayedLazyX = DelayedPlug (LazyPlug (X))

    type t = X.t face

    exception Triv of X.t
    exception Dead

    let swap pi (r, r', bdy) =
      Dim.swap pi r, Dim.swap pi r',
      DelayedLazyX.swap pi bdy

    let run rel (r, r', bdy) =
      match Rel.equate r r' rel with
      | `Same ->
        r, r',
        DelayedLazyX.run rel bdy
      | `Changed rel' ->
        r, r',
        DelayedLazyX.run rel' bdy
      | exception I.Inconsistent -> raise Dead

    let subst r x (s, s', bdy) =
      Dim.subst r x s, Dim.subst r x s',
      DelayedLazyX.subst r x bdy

    let subst_then_run rel r x (s, s', bdy) =
      let s = Dim.subst r x s in
      let s' = Dim.subst r x s' in
      match Rel.equate s s' rel with
      | `Same ->
        let bdy' = X.subst_then_run rel r x (Lazy.force @@ DelayedLazyX.drop_rel bdy) in
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

    let force rel ((r, r', bdy) as face) =
      match Rel.compare r r' rel with
      | `Same ->
        let bdy' = Lazy.force @@ DelayedLazyX.unleash bdy in
        raise @@ Triv bdy'
      | `Apart ->
        raise Dead
      | `Indet ->
        face

    let forall x (r, r', bdy) =
      let sx = `Atom x in
      if r = sx || r' = sx then None else Some (r, r', bdy)

    let gen f (r, r', bdy) =
      r, r', DelayedLazyX.make @@ lazy begin f (r, r', Delayed.drop_rel bdy) end

    let run_then_force rel (r, r', bdy) =
      match Rel.equate r r' rel with
      | `Same ->
        let bdy' = X.run rel (Lazy.force @@ DelayedLazyX.drop_rel bdy) in
        raise @@ Triv bdy'
      | `Changed rel' ->
        r, r',
        DelayedLazyX.run rel' bdy
      | exception I.Inconsistent -> raise Dead
  end

and Abs : functor (X : Domain) ->
sig
  include Domain with type t = X.t abs
  val inst : rel -> t -> dim -> X.t
end
  =
  functor (X : Domain) ->
  struct
    type t = X.t abs

    let swap pi abs =
      let Abs (x, a) = abs in
      let x' = Perm.swap_name pi x in
      let a' = X.swap pi a in
      Abs (x', a')

    let subst r z abs =
      let Abs (x, a_x) = abs in
      if z = x then
        abs
      else if I.absent x r then
        let a_x = X.subst r z a_x in
        Abs (x, a_x)
      else
        let y, pi = Perm.freshen_name x in
        let a_y = X.subst r z @@ X.swap pi a_x in
        Abs (y, a_y)

    let run rel abs =
      let Abs (x, a_x) = abs in
      let rel_x = Rel.hide' x rel in
      let a_x = X.run rel_x a_x in
      Abs (x, a_x)

    (* XXX optimize this! *)
    let subst_then_run rel r x a =
      run rel @@ subst r x a

    let inst rel abs r =
      let Abs (x, a_x) = abs in
      let rel_x = Rel.hide' x rel in
      X.subst_then_run rel_x r x a_x
  end

and AbsPlug : functor (X : DomainPlug) ->
sig
  include DomainPlug with type t = X.t abs
  val inst : rel -> t -> dim -> X.t
end
  =
  functor (X : DomainPlug) ->
  struct
    module M = Abs(X)
    include M

    let plug rel frm abs =
      let Abs (x, a_x) = abs in
      match Frame.occur1 x frm with
      | `No ->
        let rel_x = Rel.hide' x rel in
        let a_x = X.plug rel_x frm a_x in
        Abs (x, a_x)
      | `Might ->
        let y, pi = Perm.freshen_name x in
        let rel_y = rel in
        let a_y = X.plug rel_y frm @@ X.swap pi a_x in
        Abs (y, a_y)
  end

and DelayedAbsPlug : functor (X : DomainPlug) ->
sig
  include DelayedDomainPlug
    with type u = X.t abs
     and type t = X.t Delayed.t abs
  val inst : rel -> t -> dim -> X.t Delayed.t
end
  =
  functor (X : DomainPlug) ->
  struct
    type u = X.t abs
    module M = AbsPlug(DelayedPlug(X))
    include M

    module DelayedX = DelayedPlug(X)

    let make (Abs (x, v)) = Abs (x, DelayedX.make v)
    let unleash (Abs (x, v)) = Abs (x, DelayedX.unleash v)
    let drop_rel (Abs (x, v)) = Abs (x, DelayedX.drop_rel v)

    let run_then_unleash rel (Abs (x, v_x)) =
      let rel_x = Rel.hide' x rel in
      Abs (x, DelayedX.run_then_unleash rel_x v_x)
    let plug_then_unleash rel frm (Abs (x, v_x)) =
      let rel_x = Rel.hide' x rel in
      Abs (x, DelayedX.plug_then_unleash rel_x frm v_x)
  end

and DelayedPlug : functor (X : DomainPlug) ->
  DelayedDomainPlug with type u = X.t and type t = X.t Delayed.t
  =
  functor (X : DomainPlug) ->
  struct
    type u = X.t
    type t = X.t Delayed.t

    let make = Delayed.make
    let unleash = Delayed.unleash X.run
    let drop_rel = Delayed.drop_rel

    let swap pi = Delayed.fold @@ fun rel v ->
      Delayed.make' (Option.map (Perm.fold Rel.swap pi) rel) (X.swap pi v)
    let subst r x = Delayed.fold @@ fun rel v ->
      Delayed.make' (Option.map (Rel.subst' r x) rel) (X.subst r x v)
    let run rel v = Delayed.with_rel rel v
    let subst_then_run rel r x v = Delayed.make' (Some rel) (X.subst r x (Delayed.drop_rel v))

    (* it is safe to `unleash v` here, but maybe we can do `Delayed.drop_rel v`? *)
    let plug rel frm v = Delayed.make @@ X.plug rel frm (unleash v)

    let run_then_unleash rel v = X.run rel (Delayed.drop_rel v)
    let plug_then_unleash rel frm v = X.plug rel frm (unleash v) (* can we do `Delayed.drop_rel v` here? *)
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
