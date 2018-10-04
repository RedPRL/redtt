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

  (** [make v = make' None v] *)
  val make' : rel option -> 'a -> 'a t

  (** [drop_rel] is a brutal API to get the raw datum out. The caller has
      the responsibility to apply proper restrictions. *)
  val drop_rel : 'a t -> 'a

  (* [with_rel] is a convenience function to create a new delayed [X.run]
     with a new rel. *)
  val with_rel : rel -> 'a t -> 'a t

  (* [unleash] forces the result. The first argument is intended
     to be [X.run] where [X] is some structure implementing [Domain]. *)
  val unleash : (rel -> 'a -> 'a) -> 'a t -> 'a

  (* [fold] exposes the inner structure. The caller has
     the responsibility to apply proper restrictions.

     [drop_rel = fold (fun _ v -> v)] *)
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
  | Restrict of con face (* is a value when rigid *)

  | Lam of clo
  | Cons of value * value
  | ExtLam of nclo
  | RestrictThunk of con face (* is a value when rigid *)

  | Coe of {r : dim; r' : dim; ty : coe_shape; cap : value} (* is a value when (r,r') is rigid *)
  | HCom of {r : dim; r' : dim; ty : hcom_shape; cap : value; sys : con abs sys} (* is a value when (r,r') and sys are rigid *)
  | Com of {r : dim; r' : dim; ty : coe_shape; cap : value; sys : con abs sys} (* is a value when (r,r') and sys are rigid *)
  | GHCom of {r : dim; r' : dim; ty : hcom_shape; cap : value; sys : con abs sys} (* is a value when (r,r') and sys are rigid *)
  | GCom of {r : dim; r' : dim; ty : coe_shape; cap : value; sys : con abs sys} (* is a value when (r,r') and sys are rigid *)

  | Univ of {kind : Kind.t; lvl : Lvl.t}

  | V of {r : dim; ty0 : value; ty1 : value; equiv : value} (* is a value when r is an atom *)
  | VIn of {r : dim; el0 : value; el1 : value} (* is a value when r is an atom *)

  | Box of {r : dim; r' : dim; cap : value; sys : con sys} (* is a value when (r,r') and sys are rigid *)

  | Neu of {ty : value; neu : neutroid} (* is a value when neu is rigid *)

and value = con Delayed.t

and neutroid = {neu : neu Delayed.t; sys : con sys} (* is a value when sys and thus neu (by invariants) are rigid *)

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
  | NCoe of {r : dim; r' : dim; ty : neutroid abs; cap : value}
  | NHCom of {r : dim; r' : dim; ty : neutroid; cap : value; sys : con abs sys}

and frame =
  | FunApp of value
  | Fst
  | Snd
  | ExtApp of dim list
  | RestrictForce
  | VProj of {r : dim; func : value} (* rigid when r is an atom *)
  | Cap of {r : dim; r' : dim; ty : value; sys : con abs sys} (* rigid when (r,r') and sys are rigid *)

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
  (* favonia: this is a demonstration of my laziness *)
  type t = (Name.t * Name.t) list

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

  (** [swap] is a purely syntactic operation which preserves the property of being a [rel]-value. *)
  val swap : perm -> t -> t

  (** [subst] is a purely syntactic operation that does {e not} preserve the property of being a [rel]-value; it should usually be followed by [run]. *)
  val subst : dim -> Name.t -> t -> t

  (** [run] brings the prevalue underneath the restriction Ξ. *)
  val run : rel -> t -> t
end

module type DomainPlug =
sig
  include Domain

  (** [plug] applies a possibly-non-rigid value frame to a value to obtain another value. *)
  val plug : rel -> ?rigid:bool -> frame -> t -> t
end

module type DelayedDomainPlug =
sig
  (** The type [t] is intended to be the delayed version of the type [u]. *)
  type u
  include DomainPlug

  (** [make] created a delayed run. *)
  val make : u -> t

  (** [make_from_lazy] created a delayed run from a thunk. With call-by-value we need
      a separate function to pass an unevaluated expression. *)
  val make_from_lazy : u Lazy.t -> t

  (** [unleash] forces the run created by [make]. *)
  val unleash : t -> u

  (** [drop_rel] gets the underlying unrestricted raw datum. *)
  val drop_rel : t -> u

  (** Some convenience function that might be more optimized: *)

  (** [run_then_unleash rel v = unleash (run rel v)]. *)
  val run_then_unleash : rel -> t -> u

  (** [plug_then_unleash rel frm x = unleash (plug rel frm x)]. *)
  val plug_then_unleash : rel -> ?rigid:bool -> frame -> t -> u

  (** [make_then_run rel v = run rel (make v)]. *)
  val make_then_run : rel -> u -> t
end

module rec Syn :
sig
  type t = Tm.tm
  exception Triv of con

  (** [eval_dim] evaluates a dimension expression. *)
  val eval_dim : env -> t -> dim

  (** [eval] evaluates an expression.
      Invariant: everything in [env] should already be [rel]-value. *)
  val eval : rel -> env -> t -> con

  (** [eval_tm_sys] evaluates a system expression to a (possibly non-rigid)
      system value.
      Invariant: everything in [env] should already be [rel]-value. *)
  val eval_tm_sys : rel -> env -> (t, t) Tm.system -> con sys
end =
struct
  type t = Tm.tm

  exception Triv of con

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
      eval rel (Env.extend_cell env @@ Val (LazyVal.make_from_lazy v)) t

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

    | Tm.Restrict face ->
      let face = eval_tm_face rel env face in
      Restrict face

    | Tm.RestrictThunk face ->
      let face = eval_tm_face rel env face in
      RestrictThunk face

    | Tm.Univ {kind; lvl} ->
      Univ {kind; lvl}

    | Tm.V info ->
      let r = eval_dim env info.r in
      let ty0 rel0 = Val.make @@ eval rel0 env info.ty0 in
      let ty1 = Val.make @@ eval rel env info.ty1 in
      let equiv rel0 = Val.make @@ eval rel0 env info.ty1 in
      Con.make_v rel r ~ty0 ~ty1 ~equiv

    | Tm.VIn info ->
      let r = eval_dim env info.r in
      let el0 rel0 = Val.make @@ eval rel0 env info.tm0 in
      let el1 = Val.make @@ eval rel env info.tm1 in
      Con.make_vin rel r ~el0 ~el1

    | Tm.FHCom info ->
      let r = eval_dim env info.r in
      let r' = eval_dim env info.r' in
      let cap = Val.make @@ eval rel env info.cap in
      let sys = eval_bnd_sys rel env info.sys in
      Con.make_fhcom rel r r' ~cap ~sys

    | Tm.Box info ->
      let r = eval_dim env info.r in
      let r' = eval_dim env info.r' in
      let cap = Val.make @@ eval rel env info.cap in
      let sys = eval_tm_sys rel env info.sys in
      Con.make_box rel r r' ~cap ~sys

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

    | Tm.FunApp t ->
      let v = Val.make @@ eval rel env t in
      FunApp v

    | Tm.ExtApp trs ->
      let rs = List.map (eval_dim env) trs in
      ExtApp rs

    | Tm.RestrictForce ->
      RestrictForce

    | Tm.VProj info ->
      VProj
        {r = eval_dim env info.r;
         func = Val.make @@ eval rel env info.func}

    | Tm.Cap info ->
      Cap
        {r = eval_dim env info.r;
         r' = eval_dim env info.r';
         ty = Val.make @@ eval rel env info.ty;
         sys = eval_bnd_sys rel env info.sys}

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

    | Tm.Coe info ->
      let r = eval_dim env info.r in
      let r' = eval_dim env info.r' in
      let abs = eval_bnd rel env info.ty  in
      let cap = Val.make @@ eval rel env info.tm in
      Con.make_coe rel r r' ~abs ~cap

    | Tm.HCom info ->
      let r = eval_dim env info.r in
      let r' = eval_dim env info.r' in
      let ty = eval rel env info.ty in
      let cap = Val.make @@ eval rel env info.cap in
      let sys = eval_bnd_sys rel env info.sys in
      Con.make_hcom rel r r' ~ty ~cap ~sys

    | Tm.Com info ->
      let r = eval_dim env info.r in
      let r' = eval_dim env info.r' in
      let abs = eval_bnd rel env info.ty in
      let cap = Val.make @@ eval rel env info.cap in
      let sys = eval_bnd_sys rel env info.sys in
      Con.make_com rel r r' ~abs ~cap ~sys

    | Tm.GHCom info ->
      let r = eval_dim env info.r in
      let r' = eval_dim env info.r' in
      let ty = eval rel env info.ty in
      let cap = Val.make @@ eval rel env info.cap in
      let sys = eval_bnd_sys rel env info.sys in
      Con.make_ghcom rel r r' ~ty ~cap ~sys

    | Tm.GCom info ->
      let r = eval_dim env info.r in
      let r' = eval_dim env info.r' in
      let abs = eval_bnd rel env info.ty in
      let cap = Val.make @@ eval rel env info.cap in
      let sys = eval_bnd_sys rel env info.sys in
      Con.make_gcom rel r r' ~abs ~cap ~sys

    | Tm.Ix (i, _) ->
      begin
        match Env.lookup_cell_by_index i env with
        | Val v -> LazyVal.unleash v
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
          let neu = {neu = DelayedNeu.make {head = var; frames = Emp}; sys = []} in
          Neu {ty = Val.make vty; neu}
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
          let neu = {neu = DelayedNeu.make {head = var; frames = Emp}; sys = []} in
          Neu {ty = Val.make vty; neu}
      end

    | Tm.DFix _ -> raise CanJonHelpMe

  and eval_bnd_face rel env (tr, tr', bnd_opt) =
    match bnd_opt with
    | Some bnd ->
      let r = eval_dim env tr in
      let r' = eval_dim env tr' in
      let rel = Rel.equate' r r' rel in
      let env = Env.run rel env in
      let abs = lazy begin eval_bnd rel env bnd end in
      (r, r', LazyValAbs.make_from_lazy abs)
    | None -> raise PleaseRaiseProperError

  and eval_bnd_sys rel env =
    List.map (eval_bnd_face rel env)

  and eval_tm_face rel env (tr, tr', tm_opt) =
    match tm_opt with
    | Some tm ->
      let r = eval_dim env tr in
      let r' = eval_dim env tr' in
      let rel = Rel.equate' r r' rel in
      let env = Env.run rel env in
      let v = lazy begin eval rel env tm end in
      (r, r', LazyVal.make_from_lazy v)
    | None -> raise PleaseRaiseProperError

  and eval_tm_sys rel env =
    List.map (eval_tm_face rel env)
end

(** Everything in dim is a value. *)
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

(** A prevalue in [clo] is a value if its environment is a value. *)
and Clo :
sig
  include Domain with type t = clo
  val name : t -> string option

  (** [inst] will give a [rel]-value. The input [cell] must be values. *)
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

  let name (Clo {bnd = Tm.B (nm, _); _}) = nm

  let inst rel clo cell =
    let Clo {bnd; env} = clo in
    let Tm.B (_, tm) = bnd in
    Syn.eval rel (Env.extend_cell env cell) tm
end

(** A prevalue in [nclo] is a value if its environment is a value. *)
and NClo :
sig
  include Domain with type t = nclo
  val names : t -> string option bwd

  (** [inst] will give a [rel]-value. The input [cell] must be values. *)
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

  let names (NClo {bnd = Tm.NB (nms, _); _}) = nms

  let inst (rel : rel) nclo cells : con =
    let NClo {bnd; env} = nclo in
    let Tm.NB (_, tm) = bnd in
    Syn.eval rel (Env.extend_cells env cells) tm
end

(** A prevalue in [ext_clo] is a value if its environment is a value. *)
and ExtClo :
sig
  include Domain with type t = ext_clo
  val names : t -> string option bwd

  (** [inst] will give a [rel]-value. The input [cell] must be values. *)
  val inst : rel -> t -> cell list -> con * con sys

  (** [inst_then_fst rel clo cells = fst (inst rel cl cells)] *)
  val inst_then_fst : rel -> t -> cell list -> con
end =
struct
  type t = ext_clo

  let swap pi (ExtClo clo) =
    ExtClo {clo with env = Env.swap pi clo.env}

  let subst r x (ExtClo clo) =
    ExtClo {clo with env = Env.subst r x clo.env}

  let run rel (ExtClo clo) =
    ExtClo {clo with env = Env.run rel clo.env}

  let names (ExtClo {bnd = Tm.NB (nms, _); _}) = nms

  let inst rel clo cells =
    let ExtClo {bnd; env} = clo in
    let Tm.NB (_, (ty, sys)) = bnd in
    let env' = Env.extend_cells env cells in
    let vty = Syn.eval rel env' ty in
    let vsys = Syn.eval_tm_sys rel env' sys in
    vty, vsys

  let inst_then_fst rel clo cells =
    let ExtClo {bnd; env} = clo in
    let Tm.NB (_, (ty, _)) = bnd in
    let env' = Env.extend_cells env cells in
    Syn.eval rel env' ty
end

(** A cell is a value if it is [Dim r] or [Val v] for some value [v]. *)
and Cell : Domain with type t = cell =
struct
  type t = cell

  let swap pi =
    function
    | Dim d -> Dim (Dim.swap pi d)
    | Val v -> Val (LazyVal.swap pi v)

  let subst r x =
    function
    | Dim d -> Dim (Dim.subst r x d)
    | Val v -> Val (LazyVal.subst r x v)

  let run rel =
    function
    | Dim _ as c -> c
    | Val v -> Val (LazyVal.run rel v)
end

(** An environment is a value if every cell of it is. *)
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

  let swap pi env =
    {env with cells = Bwd.map (Cell.swap pi) env.cells}

  let subst r x env =
    {env with cells = Bwd.map (Cell.subst r x) env.cells}

  let run rel env =
    {env with cells = Bwd.map (Cell.run rel) env.cells}

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

  (** invariant: abs and cap are [rel]-values, but dir might not be rigid *)
  val make_coe : rel -> dim -> dim -> abs:con abs -> cap:value -> con

  (** invariant: ty, cap and sys are [rel]-values, but dir and sys might not be rigid *)
  val make_hcom : rel -> dim -> dim -> ty:con -> cap:value -> sys:con abs sys -> con

  (** invariant: abs, cap and sys are [rel]-values, but dir and sys might not be rigid *)
  val make_com : rel -> dim -> dim -> abs:con abs -> cap:value -> sys:con abs sys -> con

  (** invariant: ty, cap and sys are [rel]-values, but dir and sys might not be rigid *)
  val make_ghcom : rel -> dim -> dim -> ty:con -> cap:value -> sys:con abs sys -> con

  (** invariant: abs, cap and sys are [rel]-values, but dir and sys might not be rigid *)
  val make_gcom : rel -> dim -> dim -> abs:con abs -> cap:value -> sys:con abs sys -> con

  (** invariant: ty1 is a [rel]-value, ty0 and equiv give {rel,r=0}-values, but r:dim might not be rigid *)
  val make_v : rel -> dim -> ty0:(rel -> value) -> ty1:value -> equiv:(rel -> value) -> con

  (** invariant: el1 is a [rel]-value, el0 gives a {rel,r=0}-value, but r:dim might not be rigid *)
  val make_vin : rel -> dim -> el0:(rel -> value) -> el1:value -> con

  (** invariant: cap and sys are [rel]-values, but dir and sys might not be rigid *)
  val make_fhcom : rel -> dim -> dim -> cap:value -> sys:con abs sys -> con

  (** invariant: cap and sys are [rel]-values, but dir and sys might not be rigid *)
  val make_box : rel -> dim -> dim -> cap:value -> sys:con sys -> con
end =
struct
  module ConFace = Face (Con)
  module ConSys = Sys (Con)
  module ConAbs = AbsPlug (Con)
  module ConAbsFace = Face (ConAbs)
  module ConAbsSys = Sys (ConAbs)

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

    | Restrict face ->
      let face = ConFace.swap pi face in
      Restrict face

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

    | RestrictThunk face ->
      let face = ConFace.swap pi face in
      RestrictThunk face

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

    | GHCom info ->
      GHCom
        {r = Dim.swap pi info.r;
         r' = Dim.swap pi info.r';
         ty = HComShape.swap pi info.ty;
         cap = Val.swap pi info.cap;
         sys = ConAbsSys.swap pi info.sys}

    | GCom info ->
      GCom
        {r = Dim.swap pi info.r;
         r' = Dim.swap pi info.r';
         ty = ComShape.swap pi info.ty;
         cap = Val.swap pi info.cap;
         sys = ConAbsSys.swap pi info.sys}

    | Univ _ as con -> con

    | V info ->
      V
        {r = Dim.swap pi info.r;
         ty0 = Val.swap pi info.ty0;
         ty1 = Val.swap pi info.ty1;
         equiv = Val.swap pi info.equiv}

    | VIn info ->
      VIn
        {r = Dim.swap pi info.r;
         el0 = Val.swap pi info.el0;
         el1 = Val.swap pi info.el1}

    | Box info ->
      Box
        {r = Dim.swap pi info.r;
         r' = Dim.swap pi info.r';
         cap = Val.swap pi info.cap;
         sys = ConSys.swap pi info.sys}

    | Neu info ->
      Neu
        {ty = Val.swap pi info.ty;
         neu = Neutroid.swap pi info.neu}

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

    | Restrict face ->
      let face = ConFace.subst r x face in
      Restrict face

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

    | RestrictThunk face ->
      let face = ConFace.subst r x face in
      RestrictThunk face

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

    | GHCom info ->
      GHCom
        {r = Dim.subst r x info.r;
         r' = Dim.subst r x info.r';
         ty = HComShape.subst r x info.ty;
         cap = Val.subst r x info.cap;
         sys = ConAbsSys.subst r x info.sys}

    | GCom info ->
      GCom
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

    | Box info ->
      Box
        {r = Dim.subst r x info.r;
         r' = Dim.subst r x info.r';
         cap = Val.subst r x info.cap;
         sys = ConSys.subst r x info.sys}

    | Neu info ->
      Neu
        {ty = Val.subst r x info.ty;
         neu = Neutroid.subst r x info.neu}

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

    | Restrict face ->
      begin
        match ConFace.run rel face with
        | face -> Restrict face
        | exception ConFace.Dead -> raise PleaseRaiseProperError
      end

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

    | RestrictThunk face ->
      begin
        match ConFace.run rel face with
        | face -> RestrictThunk face
        | exception ConFace.Dead -> raise PleaseRaiseProperError
      end

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

    | GHCom info ->
      begin
        match Rel.compare info.r info.r' rel with
        | `Same ->
          Val.run_then_unleash rel info.cap
        | _ ->
          match ConAbsSys.run_then_force rel info.sys with
          | sys ->
            let cap = Val.run rel info.cap in
            let ty = HComShape.run rel info.ty in
            GHCom {info with ty; cap; sys}

          | exception ConAbsSys.Triv abs ->
            ConAbs.inst rel abs info.r'
      end

    | GCom info ->
      begin
        match Rel.compare info.r info.r' rel with
        | `Same ->
          Val.run_then_unleash rel info.cap
        | _ ->
          match ConAbsSys.run_then_force rel info.sys with
          | sys ->
            let cap = Val.run rel info.cap in
            let ty = ComShape.run rel info.ty in
            GCom {info with ty; cap; sys}

          | exception ConAbsSys.Triv abs ->
            ConAbs.inst rel abs info.r'
      end

    | Univ _ as con -> con

    | V info ->
      let ty0 rel0 = Val.run rel0 info.ty0 in
      let ty1 = Val.run rel info.ty1 in
      let equiv rel0 = Val.run rel0 info.equiv in
      make_v rel info.r ~ty0 ~ty1 ~equiv

    | VIn info ->
      let el0 rel0 = Val.run rel0 info.el0 in
      let el1 = Val.run rel info.el1 in
      make_vin rel info.r ~el0 ~el1

    | Box info ->
      begin
        match Rel.compare info.r info.r' rel with
        | `Same ->
          Val.run_then_unleash rel info.cap
        | _ ->
          match ConSys.run_then_force rel info.sys with
          | sys ->
            let cap = Val.run rel info.cap in
            Box {info with cap; sys}

          | exception ConSys.Triv c -> c
      end

    | Neu info ->
      begin
        match Neutroid.run rel info.neu with
        | neu ->
          let ty = Val.run rel info.ty in
          Neu {ty; neu}
        | exception ConSys.Triv v ->
          v
      end

  and plug rel ?(rigid=false) frm hd =
    if rigid then
      rigid_plug rel frm hd
    else
      match Frame.force rel frm ~hd with
      | `Rigid frm -> rigid_plug rel frm hd
      | `Triv c -> c

  and rigid_plug rel frm hd =
    match frm, hd with
    | FunApp arg, Lam clo ->
      Clo.inst rel clo @@ Val (LazyVal.make_from_lazy @@ lazy begin Val.unleash arg end)

    | FunApp arg, HCom {r; r'; ty = `Pi quant; cap; sys} ->
      let ty = Clo.inst rel quant.cod @@ Val (LazyVal.make_from_lazy @@ lazy begin Val.unleash arg end) in
      let cap = Val.plug rel ~rigid:true frm cap in
      let sys = ConAbsSys.plug rel ~rigid:true frm sys in
      rigid_hcom rel r r' ~ty ~cap ~sys

    | FunApp arg, Coe {r; r'; ty = `Pi abs; cap} ->
      let Abs (x, quantx) = abs in
      let y, pi = Perm.freshen_name x in
      let dom = Abs (x, Val.unleash quantx.dom) in
      let coe_arg s = make_coe rel r' s ~abs:dom ~cap:arg in
      let abs =
        let cod_y = Clo.swap pi quantx.cod in
        let coe_r'y = LazyVal.make_from_lazy @@ lazy begin coe_arg @@ `Atom y end in
        Abs (y, Clo.inst rel cod_y @@ Val coe_r'y)
      in
      let cap = Val.plug rel ~rigid:true (FunApp (Val.make @@ coe_arg r)) cap in
      rigid_coe rel r r' ~abs ~cap

    | Fst, Cons (v0, _) ->
      Val.unleash v0

    | Fst, HCom {r; r'; ty = `Sg {dom; _}; cap; sys} ->
      let ty = Val.unleash dom in
      let cap = Val.plug rel ~rigid:true Fst cap in
      let sys = ConAbsSys.plug rel ~rigid:true Fst sys in
      rigid_hcom rel r r' ~ty ~cap ~sys

    | Fst, Coe {r; r'; ty = `Sg abs; cap} ->
      let cap = Val.plug rel ~rigid:true Fst cap in
      let abs =
        let Abs (x, {dom; _}) = abs in
        Abs (x, Val.unleash dom)
      in
      rigid_coe rel r r' ~abs ~cap

    | Snd, Cons (_, v1) ->
      Val.unleash v1

    | Snd, HCom ({r; r'; ty = `Sg {dom; cod}; cap; sys} as hcom) ->
      let abs =
        let y = Name.fresh () in
        let hcom_ry_fst = LazyVal.make_from_lazy @@ lazy begin plug rel ~rigid:true Fst (HCom {hcom with r' = `Atom y}) end in
        let cod_hcom_ry_fst = Clo.inst rel cod @@ Val hcom_ry_fst in
        Abs (y, cod_hcom_ry_fst)
      in
      let cap = Val.plug rel ~rigid:true Snd cap in
      let sys = ConAbsSys.plug rel ~rigid:true Snd sys in
      rigid_com rel r r' ~abs ~cap ~sys

    | Snd, Coe ({r; r'; ty = `Sg (Abs (x, {dom = dom_x; cod = cod_x})); cap} as coe) ->
      let abs =
        let y, pi = Perm.freshen_name x in
        let coe_ry_fst = LazyVal.make_from_lazy @@ lazy begin plug rel ~rigid:true Fst (Coe {coe with r' = `Atom y}) end in
        let cod_y = Clo.swap pi cod_x in
        let cod_y_coe_ry_fst = Clo.inst rel cod_y @@ Val coe_ry_fst in
        Abs (y, cod_y_coe_ry_fst)
      in
      let cap = Val.plug rel ~rigid:true Snd cap in
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
          let cap = Val.plug rel ~rigid:true frm cap in
          let ext_sys = ConAbsSys.foreach_gen ext_sys @@
            fun (r, r', bdy) -> Abs (Name.fresh (), bdy)
          in
          let comp_sys = ConAbsSys.plug rel ~rigid:true frm sys in
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
          let cap = Val.plug rel ~rigid:true frm cap in
          let sys = ConAbsSys.foreach_gen sys_y @@
            fun (r, r', bdy_y) -> Abs (y, bdy_y)
          in
          rigid_com rel r r' ~abs ~cap ~sys
        | exception ConSys.Triv c_y ->
          run rel @@ subst r' y c_y
      end

    | RestrictForce, RestrictThunk (r, r', v) ->
      begin
        match Rel.compare r r' rel with
        | `Same -> LazyVal.unleash v
        | _ -> raise PleaseRaiseProperError
      end

    | VProj _, VIn {el1; _} ->
      Val.unleash el1

    | Cap _, Box {cap; _} ->
      Val.unleash cap

    | _, Neu info ->
      let neu = Neutroid.plug rel ~rigid:true frm info.neu in
      let ty, sys = rigid_plug_ty rel frm info.ty hd in
      Neu {ty = Val.make ty; neu = {neu with sys = sys @ neu.sys}}

    | FunApp _, _ -> raise PleaseRaiseProperError
    | Fst, _ -> raise PleaseRaiseProperError
    | Snd, _ -> raise PleaseRaiseProperError
    | ExtApp _, _ -> raise PleaseRaiseProperError
    | RestrictForce, _ -> raise PleaseRaiseProperError
    | VProj _, _ -> raise PleaseRaiseProperError
    | Cap _, _ -> raise PleaseRaiseProperError

  and rigid_plug_ty rel frm ty hd =
    match Val.unleash ty, frm with
    | Pi {dom; cod}, FunApp arg ->
      let arg = lazy begin Val.unleash arg end in
      Clo.inst rel cod @@ Val (LazyVal.make_from_lazy arg), []

    | Pi _, _ -> raise PleaseRaiseProperError

    | Sg {dom; _}, Fst ->
      Val.unleash dom, []

    | Sg {cod; _}, Snd ->
      let fst = lazy begin plug rel ~rigid:true Fst hd end in
      Clo.inst rel cod @@ Val (LazyVal.make_from_lazy fst), []

    | Sg _, _ -> raise PleaseRaiseProperError

    | Ext extclo, ExtApp rs ->
      ExtClo.inst rel extclo @@ List.map (fun r -> Dim r) rs

    | Ext _, _ -> raise PleaseRaiseProperError

    | Restrict (r, r', ty), RestrictForce ->
      LazyVal.unleash ty, [(r, r', LazyVal.make hd)]

    | V {ty1; _}, VProj _ ->
      Val.unleash ty1, []

    | HCom {ty = `Pos; cap; _}, Cap _ ->
      Val.unleash cap, []

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
      match ConAbsSys.force rel sys with
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

  and make_ghcom rel r r' ~ty ~cap ~sys =
    match Rel.compare r r' rel with
    | `Same ->
      Val.unleash cap
    | _ ->
      match ConAbsSys.force rel sys with
      | _ ->
        rigid_ghcom rel r r' ~ty ~cap ~sys
      | exception ConAbsSys.Triv abs ->
        ConAbs.inst rel abs r'

  and make_gcom rel r r' ~abs ~cap ~sys =
    match Rel.compare r r' rel with
    | `Same ->
      Val.unleash cap
    | _ ->
      match ConAbsSys.force rel sys with
      | _ ->
        rigid_gcom rel r r' ~abs ~cap ~sys
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

  and make_fhcom rel r r' ~cap ~sys =
    match Rel.compare r r' rel with
    | `Same ->
      Val.unleash cap
    | _ ->
      match ConAbsSys.force rel sys with
      | _ ->
        HCom {r; r'; ty = `Pos; cap; sys}
      | exception ConAbsSys.Triv abs ->
        ConAbs.inst rel abs r'

  and make_box rel r r' ~cap ~sys =
    match Rel.compare r r' rel with
    | `Same ->
      Val.unleash cap
    | _ ->
      match ConSys.force rel sys with
      | _ ->
        Box {r; r'; cap; sys}
      | exception ConSys.Triv c -> c

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

    | V info ->
      let rel0 = Rel.equate' r `Dim0 rel in
      let func = Val.plug rel0 ~rigid:true Fst info.equiv in
      let vproj = VProj {r; func} in

      let hcom0 r' = make_hcom rel0 r r' ~ty:(Val.unleash info.ty0) ~cap:(Val.run rel0 cap) ~sys:(ConAbsSys.run rel0 sys) in
      let el0 = Val.make @@ hcom0 r' in
      let el1 = Val.make @@
        let cap = Val.plug rel ~rigid:true vproj cap in
        let face0 =
          r, `Dim0,
          lazy begin
            let y = Name.fresh () in
            let arg0 = FunApp (Val.make @@ hcom0 @@ `Atom y) in
            let bdy_y = Val.plug rel0 ~rigid:true arg0 func in
            Abs (y, bdy_y)
          end
        in
        let sys = ConAbsSys.plug rel ~rigid:true vproj sys in
        rigid_hcom rel r r' ~ty:(Val.unleash info.ty1) ~cap ~sys
      in
      VIn {r; el0; el1}

    | HCom {ty = `Pos; _} ->
      raise CanFavoniaHelpMe

    | Neu info ->
      let neu = DelayedNeu.make
        {head = NHCom {r; r'; ty = info.neu; cap; sys};
         frames = Emp}
      in
      let neu_sys =
        let cap_face = r, r', LazyVal.make_from_lazy @@ lazy begin Val.unleash cap end in
        let tube_faces =
          ConSys.foreach_gen sys @@ fun (s, s', abs) ->
          let rel' = Rel.equate' s s' rel in
          ConAbs.inst rel' abs r'
        in
        let old_faces =
          ListUtil.foreach info.neu.sys @@ ConFace.gen @@ fun (s, s', bdy) ->
          let rel' = Rel.equate' s s' rel in
          let ty = run rel' bdy in
          let cap = Val.run rel' cap in
          let sys = ConAbsSys.run rel' sys in
          make_hcom rel' r r' ~ty ~cap ~sys
        in
        cap_face :: tube_faces @ old_faces
      in
      Neu {ty = Val.make ty; neu = {neu; sys = neu_sys}}

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
      let neu = DelayedNeu.make
        {head = NCoe {r; r'; ty = Abs (x, info.neu); cap};
         frames = Emp}
      in
      let ty = Val.make_then_run rel (Con.subst r' x tyx) in
      let sys =
        let cap_face = r, r', LazyVal.make_from_lazy @@ lazy begin Val.unleash cap end in
        let old_faces =
          ListUtil.foreach (ConSys.forall x info.neu.sys) @@ ConFace.gen @@ fun (s, s', bdy) ->
          let rel' = Rel.equate' s s' rel in
          let abs = ConAbs.run rel' @@ Abs (x, bdy) in
          let cap = Val.run rel' cap in
          make_coe rel' r r' ~abs ~cap
        in
        cap_face :: old_faces
      in
      Neu {ty; neu = {neu; sys}}

    | _ ->
      raise PleaseRaiseProperError

  and expand_rigid_com rel r r' ~abs ~cap ~sys =
    let ty = ConAbs.inst rel abs r' in
    let cap = Val.make @@ make_coe rel r r' ~abs ~cap in
    let sys =
      let Abs (bound_var_of_abs, _) = abs in
      ConAbsSys.foreach_gen sys @@ fun (r, r', face) ->
      let rel' = Rel.equate r r' in
      let Abs (y, bdy_y) = face in
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

    | Univ _ as ty -> rigid_hcom rel r r' ~ty ~cap ~sys

    | V _ | HCom {ty = `Pos; _} -> expand_rigid_com rel r r' ~abs ~cap ~sys

    | Neu _ -> expand_rigid_com rel r r' ~abs ~cap ~sys (* really too complicated *)

    | _ ->
      raise PleaseRaiseProperError

  and expand_rigid_ghcom rel s s' ~ty ~cap ~sys =
    match sys with
    | [] -> Val.unleash cap
    | (r, r', abs) :: rest ->
      let make_abs gen = LazyValAbs.make_from_lazy @@ lazy begin let y = Name.fresh () in Abs (y, gen @@ `Atom y) end in
      let face rel0 (dim0, dim1) r' = (* [dim0] and [dim1] will be swapped to generate the symmetric case. *)
        let bdy00 rel00 r' = ConAbs.inst rel00 (LazyValAbs.drop_rel abs) r' in
        let bdy01 rel01 r' =
          make_ghcom rel01 r r' ~ty:(Con.run rel01 ty) ~cap:(Val.run rel01 cap) ~sys:(ConAbsSys.run rel01 rest)
        in
        match Rel.equate r' dim0 rel0 with
        | `Same -> bdy00 rel0 r'
        | exception I.Inconsistent -> bdy01 rel0 r'
        | `Changed rel00 ->
          let rel01 = Rel.equate' r' dim1 rel0 in
          let ty = Con.run rel0 ty in
          let cap = Val.run rel0 cap in
          let sys =
            (r', dim0, LazyValAbs.run rel00 abs) ::
            (r', dim1, make_abs @@ bdy01 rel01) ::
            ConAbsSys.run rel0 rest
          in
          make_hcom rel0 r r' ~ty ~cap ~sys
      in
      match Rel.equate r `Dim0 rel with
      | `Same -> face rel (`Dim0, `Dim1) r'
      | exception I.Inconsistent -> face rel (`Dim1, `Dim0) r'
      | `Changed rel0 ->
        let rel1 = Rel.equate' r `Dim1 rel in
        let sys =
          (r, `Dim0, make_abs @@ face rel0 @@ (`Dim0, `Dim1)) ::
          (r, `Dim1, make_abs @@ face rel1 @@ (`Dim1, `Dim0)) :: rest
        in
        make_hcom rel r r' ~ty ~cap ~sys

  and rigid_ghcom rel r r' ~ty ~cap ~sys =
    match ty with
    | Sg quant ->
      GHCom {r; r'; ty = `Sg quant; cap; sys}

    | Pi quant ->
      GHCom {r; r'; ty = `Pi quant; cap; sys}

    | Ext extclo ->
      GHCom {r; r'; ty = `Ext extclo; cap; sys}

    | Univ _ | HCom {ty = `Pos; _} | V _ ->
      expand_rigid_ghcom rel r r' ~ty ~cap ~sys

    | Neu _ ->
      expand_rigid_ghcom rel r r' ~ty ~cap ~sys

    | _ ->
      raise PleaseRaiseProperError

  and expand_rigid_gcom rel r r' ~abs ~cap ~sys =
    let ty = ConAbs.inst rel abs r' in
    let cap = Val.make @@ make_coe rel r r' ~abs ~cap in
    let sys =
      let Abs (bound_var_of_abs, _) = abs in
      ConAbsSys.foreach_gen sys @@ fun (r, r', face) ->
      let rel' = Rel.equate r r' in
      let Abs (y, bdy_y) = face in
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
    rigid_ghcom rel r r' ~ty ~cap ~sys

  and rigid_gcom rel r r' ~abs ~cap ~sys =
    let Abs (x, tyx) = abs in
    match tyx with
    | Sg quant ->
      GCom {r; r'; ty = `Sg (Abs (x, quant)); cap; sys}

    | Pi quant ->
      GCom {r; r'; ty = `Pi (Abs (x, quant)); cap; sys}

    | Ext extclo ->
      GCom {r; r'; ty = `Ext (Abs (x, extclo)); cap; sys}

    | Univ _ as ty -> expand_rigid_ghcom rel r r' ~ty ~cap ~sys

    | V _ | HCom {ty = `Pos; _} -> expand_rigid_gcom rel r r' ~abs ~cap ~sys

    | Neu _ -> expand_rigid_gcom rel r r' ~abs ~cap ~sys (* really too complicated *)

    | _ ->
      raise PleaseRaiseProperError
end

and Val : DelayedDomainPlug
  with type u = con
   and type t = con Delayed.t
  = DelayedPlug (Con)

and LazyVal : DelayedDomainPlug
  with type u = con
   and type t = con Lazy.t Delayed.t
  = DelayedLazyPlug (Con)

and LazyValAbs : DelayedDomainPlug
  with type u = con abs
   and type t = con abs Lazy.t Delayed.t
  = DelayedLazyPlug (AbsPlug (Con))

(** A [coe_shape] is a value when its component is. *)
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

(** A [hcom_shape] is a value when its component is. *)
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

and ComShape : Domain with type t = com_shape = CoeShape

(** A [quantifier] is a value when both of its components are. *)
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
end

(** A [neu] is a value if its head and frames are rigid values. *)
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

  let plug rel ?(rigid=false) frm neu =
    if rigid then
      {neu with
       frames = neu.frames #< frm}
    else
      raise PleaseRaiseProperError
end

(* A [neutroid] is a value if everything is rigid. *)
and Neutroid :
sig
  include DomainPlug with type t = neutroid

  exception Triv of con
end =
struct
  type t = neutroid

  module ConSys = Sys (Con)
  exception Triv = ConSys.Triv

  let swap pi {neu; sys} =
    {neu = DelayedNeu.swap pi neu;
     sys = ConSys.swap pi sys}

  let run rel {neu; sys} =
    (* The system needs to be forced first. The invariant is that
     * if [sys] is rigid, it is safe to run neu *)
    let sys = ConSys.run_then_force rel sys in
    let neu = DelayedNeu.run rel neu in
    {neu; sys}

  let subst r x {neu; sys} =
    {neu = DelayedNeu.subst r x neu;
     sys = ConSys.subst r x sys}

  let plug rel ?(rigid=false) frm {neu; sys} =
    if rigid then
      {neu = DelayedNeu.plug ~rigid rel frm neu;
       sys = ConSys.plug ~rigid rel frm sys}
    else
      raise PleaseRaiseProperError
end

and DelayedNeu : DelayedDomainPlug with type u = neu and type t = neu Delayed.t =
  DelayedPlug (Neu)

(** A [head] is a value if its components are rigid values.

   [Head.plug] assumes the input frame is rigid. *)
and Head : Domain with type t = head =
struct
  type t = head

  module NeutroidAbs = Abs (Neutroid)
  module ConAbsSys = Sys (AbsPlug (Con))

  let swap pi =
    function
    | Lvl _ | Var _ | Meta _ as h -> h
    | NCoe info ->
      NCoe
        {r = Dim.swap pi info.r;
         r' = Dim.swap pi info.r';
         ty = NeutroidAbs.swap pi info.ty;
         cap = Val.swap pi info.cap}
    | NHCom info ->
      NHCom
        {r = Dim.swap pi info.r;
         r' = Dim.swap pi info.r';
         ty = Neutroid.swap pi info.ty;
         cap = Val.swap pi info.cap;
         sys = ConAbsSys.swap pi info.sys}

  let run rel =
    function
    | Lvl _ | Var _ | Meta _ as h -> h
    | NCoe info ->
      NCoe
        {r = Dim.run rel info.r;
         r' = Dim.run rel info.r';
         ty = NeutroidAbs.run rel info.ty;
         cap = Val.run rel info.cap}
    | NHCom info ->
      NHCom
        {r = Dim.run rel info.r;
         r' = Dim.run rel info.r';
         ty = Neutroid.run rel info.ty;
         cap = Val.run rel info.cap;
         sys = ConAbsSys.run rel info.sys}

  let subst r x =
    function
    | Lvl _ | Var _ | Meta _ as h -> h
    | NCoe info ->
      NCoe
        {r = Dim.subst r x info.r;
         r' = Dim.subst r x info.r';
         ty = NeutroidAbs.subst r x info.ty;
         cap = Val.subst r x info.cap}
    | NHCom info ->
      NHCom
        {r = Dim.subst r x info.r;
         r' = Dim.subst r x info.r';
         ty = Neutroid.subst r x info.ty;
         cap = Val.subst r x info.cap;
         sys = ConAbsSys.subst r x info.sys}
end

(** A [frame] is a value if its components are. It itself might not be rigid. *)
and Frame :
sig
  include Domain with type t = frame

  val occur1 : Name.t -> frame -> [`No | `Might]
  val occur : Name.t bwd -> frame -> [`No | `Might]

  (* OCaml compiler is not happy about [exception Triv of con]
   * because of the lack of safe modules in the cycle
   * Frame -> Sys -> Face -> Frame. Therefore we were using
   * {[[`Rigid of t | `Triv of con]]} below. *)
  val force : rel -> t -> hd:con -> [`Rigid of t | `Triv of con]
end =
struct
  type t = frame

  module ConAbs = AbsPlug (Con)
  module ConAbsSys = Sys (AbsPlug (Con))

  let swap pi =
    function
    | FunApp arg ->
      let arg = Val.swap pi arg in
      FunApp arg
    | Fst | Snd as frm ->
      frm
    | ExtApp rs ->
      let rs = List.map (Dim.swap pi) rs in
      ExtApp rs
    | RestrictForce ->
      RestrictForce
    | VProj info ->
      VProj
        {r = Dim.swap pi info.r;
         func = Val.swap pi info.func}
    | Cap info ->
      Cap
        {r = Dim.swap pi info.r;
         r' = Dim.swap pi info.r';
         ty = Val.swap pi info.ty;
         sys = ConAbsSys.swap pi info.sys}

  let subst r x =
    function
    | FunApp arg ->
      let arg = Val.subst r x arg in
      FunApp arg
    | Fst | Snd as frm ->
      frm
    | ExtApp rs ->
      let rs = List.map (Dim.subst r x) rs in
      ExtApp rs
    | RestrictForce ->
      RestrictForce
    | VProj info ->
      VProj
        {r = Dim.subst r x info.r;
         func = Val.subst r x info.func}
    | Cap info ->
      Cap
        {r = Dim.subst r x info.r;
         r' = Dim.subst r x info.r';
         ty = Val.subst r x info.ty;
         sys = ConAbsSys.subst r x info.sys}

  let run rel =
    function
    | FunApp arg ->
      let arg = Val.run rel arg in
      FunApp arg
    | Fst | Snd | ExtApp _ | RestrictForce as frm ->
      frm
    | VProj info ->
      let r = Dim.run rel info.r in
      let func =
        match Rel.equate' r `Dim0 rel with
        | rel -> Val.run rel info.func
        | exception I.Inconsistent -> info.func
      in
      VProj {r; func}
    | Cap info ->
      Cap
        {r = Dim.run rel info.r;
         r' = Dim.run rel info.r';
         ty = Val.run rel info.ty;
         sys = ConAbsSys.run rel info.sys}

  let occur xs =
    function
    | FunApp _ | VProj _ | Cap _ ->
      `Might
    | Fst | Snd | RestrictForce ->
      `No
    | ExtApp dims ->
      if Bwd.for_all (fun x -> List.for_all (I.absent x) dims) xs then
        `No
      else
        `Might

  let occur1 x = occur (Emp #< x)

  let force rel frm ~hd =
    match frm with
    | FunApp _ | Fst | Snd | ExtApp _ | RestrictForce ->
      `Rigid frm
    | VProj {r; func} ->
      begin
        match Rel.compare r `Dim0 rel with
        | `Same -> `Triv (Val.plug_then_unleash rel (FunApp (Val.make hd)) func)
        | `Apart -> `Triv hd
        | `Indet -> `Rigid frm
      end
    | Cap {r; r'; ty; sys} ->
      begin
        match Rel.compare r r' rel with
        | `Same ->
          `Triv hd
        | _ ->
          match ConAbsSys.force rel sys with
          | sys -> `Rigid frm
          | exception ConAbsSys.Triv abs ->
            `Triv (Con.make_coe rel r' r ~abs ~cap:(Val.make hd))
      end

end

(** A [sys] is a value if its elements are. It itself might not be rigid.

    [Sys.plug] should send rigid systems to rigid systems. *)
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

    (** [run_then_force rel sys = force rel (run rel sys)] *)
    val run_then_force : rel -> t -> t

    (** [foreach_gen sys f = ListUtil.foreach sys (Face.gen f)] *)
    val foreach_gen : 'a sys -> (dim * dim * 'a -> X.t) -> t
  end =
  functor (X : DomainPlug) ->
  struct
    type t = X.t sys
    module Face = Face (X)

    exception Triv = Face.Triv

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

    let plug rel ?(rigid=false) frm sys =
      List.map (Face.plug rel ~rigid frm) sys

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

    let foreach_gen sys f = ListUtil.foreach sys (Face.gen f)
  end

(** A [face] is a value if its elements are. It itself might not be rigid. *)
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

    (** [gen] makes it easy to hook up [run], assuming the provided function
        will then sufficiently restrict the body. the body fed into the externally
        function might be less restricted then the previous run or the cobifration
        suggests. {e Note that this will not force the generated face.} *)
    val gen : (dim * dim * 'a -> X.t) -> 'a face -> t

    (** Some convenience functions which could be more efficient: *)

    (** [run_then_force rel face = force (run rel face)] *)
    val run_then_force : rel -> t -> t
  end =
  functor (X : DomainPlug) ->
  struct
    module DelayedLazyX = DelayedLazyPlug (X)

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

    let plug rel ?(rigid=false) frm (r, r', bdy) =
      match Rel.equate r r' rel with
      | `Same ->
        r, r',
        DelayedLazyX.plug rel ~rigid frm bdy
      | `Changed rel' ->
        r, r',
        let frm' = Frame.run rel' frm in
        DelayedLazyX.plug rel' frm' bdy

    let force rel ((r, r', bdy) as face) =
      match Rel.compare r r' rel with
      | `Same ->
        raise @@ Triv (DelayedLazyX.unleash bdy)
      | `Apart ->
        raise Dead
      | `Indet ->
        face

    let forall x (r, r', bdy) =
      let sx = `Atom x in
      if r = sx || r' = sx then None else Some (r, r', bdy)

    let gen f (r, r', bdy) =
      r, r', DelayedLazyX.make_from_lazy @@ lazy begin f (r, r', Lazy.force @@ Delayed.drop_rel bdy) end

    let run_then_force rel v = force rel (run rel v)
  end

(** [Abs (x, a)] is a [rel]-value if [a] is a [(Rel.hide' x rel)]-value. *)
and Abs : functor (X : Domain) ->
sig
  include Domain with type t = X.t abs

  (** [inst] will give a [rel]-value. The inputs can be non-values. *)
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

    let inst rel abs r =
      let Abs (x, a_x) = abs in
      let rel_x = Rel.hide' x rel in
      X.run rel_x @@ X.subst r x a_x
  end

and AbsPlug : functor (X : DomainPlug) ->
sig
  include DomainPlug with type t = X.t abs

  (** [inst] will give a [rel]-value. The inputs can be non-values. *)
  val inst : rel -> t -> dim -> X.t
end
  =
  functor (X : DomainPlug) ->
  struct
    module M = Abs(X)
    include M

    let plug rel ?(rigid=false) frm abs =
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

  (** [inst] will give a [rel]-value. The inputs can be non-values. *)
  val inst : rel -> t -> dim -> X.t Delayed.t
end
  =
  functor (X : DomainPlug) ->
  struct
    type u = X.t abs
    module M = AbsPlug(DelayedPlug(X))
    include M

    module DelayedX = DelayedPlug(X)

    let make (Abs (x, a)) = Abs (x, DelayedX.make a)

    let make_from_lazy (lazy v) = make v

    let unleash (Abs (x, a)) = Abs (x, DelayedX.unleash a)

    let drop_rel (Abs (x, a)) = Abs (x, DelayedX.drop_rel a)

    let run_then_unleash rel (Abs (x, a_x)) =
      let rel_x = Rel.hide' x rel in
      Abs (x, DelayedX.run_then_unleash rel_x a_x)

    let plug_then_unleash rel ?(rigid=false) frm v =
      unleash @@ plug rel ~rigid frm v

    let make_then_run rel abs = run rel (make abs)
  end

and DelayedPlug : functor (X : DomainPlug) ->
  DelayedDomainPlug with type u = X.t and type t = X.t Delayed.t
  =
  functor (X : DomainPlug) ->
  struct
    type u = X.t
    type t = X.t Delayed.t

    let make = Delayed.make

    let make_from_lazy (lazy v) = Delayed.make v

    let unleash = Delayed.unleash X.run

    let drop_rel = Delayed.drop_rel

    let swap pi =
      Delayed.fold @@ fun rel v ->
      Delayed.make' (Option.map (Perm.fold Rel.swap pi) rel) (X.swap pi v)

    let subst r x =
      Delayed.fold @@ fun rel v ->
      Delayed.make' (Option.map (Rel.subst' r x) rel) (X.subst r x v)

    let run rel v = Delayed.with_rel rel v

    let make_then_run rel = Delayed.make' (Some rel)

    let plug rel ?(rigid=false) frm v = Delayed.make @@ X.plug rel ~rigid frm (unleash v)

    let run_then_unleash rel v = X.run rel (Delayed.drop_rel v)

    let plug_then_unleash rel ?(rigid=false) frm v = X.plug rel ~rigid frm (unleash v)
  end

and DelayedLazyPlug : functor (X : DomainPlug) ->
  DelayedDomainPlug with type u = X.t and type t = X.t Lazy.t Delayed.t =
  functor (X : DomainPlug) ->
  struct
    type u = X.t
    type t = X.t Lazy.t Delayed.t

    let make v = Delayed.make @@ lazy v

    let make_from_lazy = Delayed.make

    let unleash v = Lazy.force @@ Delayed.unleash (fun rel v -> lazy begin X.run rel (Lazy.force v) end) v

    let drop_rel v = Lazy.force (Delayed.drop_rel v)

    let swap pi =
      Delayed.fold @@ fun rel v ->
      Delayed.make' (Option.map (Perm.fold Rel.swap pi) rel) @@ lazy begin X.swap pi (Lazy.force v) end

    let subst r x =
      Delayed.fold @@ fun rel v ->
      Delayed.make' (Option.map (Rel.subst' r x) rel) @@ lazy begin X.subst r x (Lazy.force v) end

    let run rel v = Delayed.with_rel rel v

    let make_then_run rel v = Delayed.make' (Some rel) (lazy v)

    let plug rel ?(rigid=false) frm v = Delayed.make @@ lazy begin X.plug rel ~rigid frm (unleash v) end

    let run_then_unleash rel v = X.run rel (drop_rel v)

    let plug_then_unleash rel ?(rigid=false) frm v = X.plug rel ~rigid frm (unleash v)
  end

module ConAbs = AbsPlug (Con)
