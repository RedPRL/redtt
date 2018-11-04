open RedBasis
open Bwd
open BwdNotation
open Combinators

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
 * however, if the concrete type is known (for example [con Delayed.t]),
 * the corresponding module (for example [Val]) should be used.
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
  | Restrict of con face (* is a value even if the face is not rigid *)

  | Lam of clo
  | Cons of value * value
  | ExtLam of nclo
  | RestrictThunk of con face (* is a value even if the face is not rigid *)

  | Coe of {r : dim; r' : dim; ty : coe_shape; cap : value} (* is a value when (r,r') is rigid *)
  | HCom of {r : dim; r' : dim; ty : hcom_shape; cap : value; sys : con abs sys} (* is a value when (r,r') and sys are rigid *)
  | Com of {r : dim; r' : dim; ty : com_shape; cap : value; sys : con abs sys} (* is a value when (r,r') and sys are rigid *)
  | GHCom of {r : dim; r' : dim; ty : hcom_shape; cap : value; sys : con abs sys} (* is a value when (r,r') and sys are rigid *)
  | GCom of {r : dim; r' : dim; ty : com_shape; cap : value; sys : con abs sys} (* is a value when (r,r') and sys are rigid *)

  | Univ of {kind : Kind.t; lvl : Lvl.t}

  | V of {r : dim; ty0 : value; ty1 : value; equiv : value} (* is a value when r is an atom *)
  | VIn of {r : dim; el0 : value; el1 : value} (* is a value when r is an atom *)

  | Box of {r : dim; r' : dim; cap : value; sys : con sys} (* is a value when (r,r') and sys are rigid *)

  | Neu of {ty : value; neu : neutroid} (* is a value when neu is rigid *)

  | FortyTwo (* a dummy filler to signal that something might be terribly wrong *)

  | Data of {lbl : Name.t; strict : bool; params : cell list; constrs : GlobalEnv.t * Desc.constrs}
  | Intro of {dlbl : Name.t; clbl : string; args : constr_cell list; sys : con sys}


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
  | NCoeData of {r : dim; r' : dim; ty : con abs; cap : neutroid}
  | NHCom of {r : dim; r' : dim; ty : neutroid; cap : value; sys : con abs sys}

and frame =
  | FunApp of typed_value (* annotated if ty != None *)
  | Fst
  | Snd
  | ExtApp of dim list
  | RestrictForce
  | VProj of {r : dim; func : typed_value} (* rigid when r is an atom *)
  | Cap of {r : dim; r' : dim; ty : value; sys : con abs sys} (* rigid when (r,r') and sys are rigid *)
  | Elim of {lbl : Name.t; params : cell list; mot : clo; clauses : (string * nclo) list}

and typed_value =
  {ty : value option;
   value : value}

and neu =
  {head : head;
   frames : frame bwd} (* the TypedVal in the frames here must be fully annotated. *)

and cell =
  [ `Val of con Lazy.t Delayed.t
  | `Dim of dim
  ]

and constr_cell =
  [ `Const of value
  | `Rec of constr_rec_spec * value
  | `Dim of dim
  ]

and constr_rec_spec =
  [ `Self ]

and env = {globals : GlobalEnv.t; cells : cell bwd}

and clo = Clo of {bnd : Tm.tm Tm.bnd; env : env}
and nclo = NClo of {bnd : Tm.tm Tm.nbnd; env : env}
and ext_clo = ExtClo of {bnd : (Tm.tm * (Tm.tm, Tm.tm) Tm.system) Tm.nbnd; env : env}



type error =
  | ExpectedDimension
  | UnexpectedDimension
  | MalformedConstructorArguments
  | ExpectedTypeAnnotation
  | GlobalVariableWrongKind
  | UnexpectedDeadFace
  | InvalidRestrictionProjection
  | PlugMismatch of {frm : frame; con : con}
  | PlugTyMismatch of {frm : frame; tycon : con}

exception E of error



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

  let rec freshen_names =
    function
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

  (* TODO: this should not take a 'rel'. [pp] is meant to be simple-minded. *)
  val pp : t Pp.t0
end

module type DomainPlug =
sig
  include Domain

  (** [plug] applies a possibly-non-rigid value frame to a value to obtain another value.
      Annotations in TypedVal in the frame will be ignored and regenerated when needed. *)
  val plug : rel -> rigid:bool -> frame -> t -> t
end

(** TODO standarize [inst] and [inst_then_unleash] *)

module type DelayedDomainPlug =
sig
  (** The type [t] is intended to be the delayed version of the type [u]. *)
  type u
  include DomainPlug

  (** [make] creates a delayed run. *)
  val make : u -> t

  (** [make_from_lazy] creates a delayed run from a thunk. With call-by-value we need
      a separate function to pass an unevaluated expression. *)
  val make_from_lazy : u Lazy.t -> t

  (** [make_from_delayed] creates a delayed run from another delayed run. *)
  val make_from_delayed : u Delayed.t -> t

  (** [unleash] forces the run created by [make]. *)
  val unleash : t -> u

  (** [drop_rel] gets the underlying unrestricted raw datum. *)
  val drop_rel : t -> u

  (** Some convenience function that might be more optimized: *)

  (** [run_then_unleash rel v = unleash (run rel v)]. *)
  val run_then_unleash : rel -> t -> u

  (** [plug_then_unleash rel frm x = unleash (plug rel frm x)]. *)
  val plug_then_unleash : rel -> rigid:bool -> frame -> t -> u

  (** [make_then_run rel v = run rel (make v)]. *)
  val make_then_run : rel -> u -> t
end

module rec Error :
sig
  type t = error
  val pp : t Pp.t0
end =
struct

  type t = error

  let pp fmt =
    function
    | ExpectedDimension ->
      Format.fprintf fmt "Expected dimension"
    | UnexpectedDimension ->
      Format.fprintf fmt "Unexpected dimension"
    | MalformedConstructorArguments ->
      Format.fprintf fmt "Constructor arguments did not match expected structure"
    | ExpectedTypeAnnotation ->
      Format.fprintf fmt "Expected type annotation"
    | GlobalVariableWrongKind ->
      Format.fprintf fmt "Global variable has wrong kind"
    | UnexpectedDeadFace ->
      Format.fprintf fmt "Encountered unexpected dead face"
    | InvalidRestrictionProjection ->
      Format.fprintf fmt "Tried to project from untrue restriction"
    | PlugMismatch {frm; con} ->
      Format.fprintf fmt "Frame %a does not operate on element %a" Frame.pp frm Con.pp con
    | PlugTyMismatch {frm; tycon} ->
      Format.fprintf fmt "Frame %a does not operate on type %a" Frame.pp frm Con.pp tycon


  let _ =
    PpExn.install_printer @@ fun fmt ->
    function
    | E err ->
      Format.fprintf fmt "@[<1>%a@]" pp err
    | _ ->
      raise PpExn.Unrecognized

end


and Syn :
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

  module ConSys = Sys (Con)

  let rec eval_dim env t =
    match Tm.unleash t with
    | Tm.Dim0 -> `Dim0
    | Tm.Dim1 -> `Dim1
    | Tm.Up (Tm.Ix (i, _), []) ->
      begin
        match Env.lookup_cell_by_index i env with
        | `Dim r -> r
        | _ -> raise @@ E ExpectedDimension
      end
    | Tm.Up (Tm.Var {name; _}, []) -> `Atom name
    | Tm.Up (Tm.DownX r, []) -> eval_dim env r
    | _ -> raise @@ E ExpectedDimension


  module ConAbs = Abs(Con)

  let rec eval rel env t =
    match Tm.unleash t with
    | Tm.Up cmd ->
      eval_cmd rel env cmd

    | Tm.Let (c, Tm.B (_, t)) ->
      let v = lazy begin eval_cmd rel env c end in
      eval rel (Env.extend_cell env @@ Cell.lazy_con v) t

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
      raise @@ E UnexpectedDimension

    | Tm.Restrict face ->
      let face = eval_tm_face_ rel env face in
      Restrict face

    | Tm.RestrictThunk face ->
      let face = eval_tm_face_ rel env face in
      RestrictThunk face

    | Tm.Univ {kind; lvl} ->
      Univ {kind; lvl}

    | Tm.V info ->
      let r = eval_dim env info.r in
      let ty0 rel0 = Val.make @@ eval rel0 env info.ty0 in
      let ty1 = Val.make @@ eval rel env info.ty1 in
      let equiv rel0 = Val.make @@ eval rel0 env info.equiv in
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

    | Tm.Data info ->
      let desc = GlobalEnv.lookup_datatype env.globals info.lbl in
      let strict = Desc.is_strict_set desc in
      let params =
        flip List.map info.params @@ fun t ->
        Cell.lazy_con @@ lazy begin eval rel env t end
      in
      Data {lbl = info.lbl; strict; params; constrs = env.globals, Desc.constrs desc}

    | Tm.Intro (dlbl, clbl, params, args) ->
      let desc = GlobalEnv.lookup_datatype env.globals dlbl in
      let constr = Desc.lookup_constr clbl @@ Desc.constrs desc in
      let eval_as_cell t = Cell.lazy_con @@ lazy (eval rel env t) in
      let params = List.map eval_as_cell params in
      let tyenv = Env.extend_cells (Env.init env.globals) params in
      let benv, args = eval_constr_args rel ~env ~tyenv ~constr ~args in
      let sys = eval_tm_sys rel benv @@ Desc.Constr.boundary constr in
      Con.make_intro rel ~dlbl ~clbl ~args ~sys

    | Tm.FortyTwo -> FortyTwo

  and eval_constr_args rel ~env ~tyenv ~constr ~args =
    let rec go acc tyenv (tele : Desc.constr) tms =
      match tele, tms with
      | Desc.TNil _, [] ->
        tyenv, Bwd.to_list acc
      | Desc.TCons (`Const ty, Tm.B (_, tele)), tm :: tms ->
        let vty = lazy begin eval rel tyenv ty end in
        let el = lazy begin eval rel env tm end in
        let acc = acc #< (`Const (Val.make_from_lazy el)) in
        let tyenv = Env.extend_cell tyenv @@ Cell.lazy_con el in
        go acc tyenv tele tms
      | Desc.TCons (`Rec Desc.Self, Tm.B (_, tele)), tm :: tms ->
        let el = lazy begin eval rel env tm end in
        let tyenv = Env.extend_cell tyenv @@ Cell.lazy_con el in
        let acc = acc #< (`Rec (`Self, Val.make_from_lazy el)) in
        go acc tyenv tele tms
      | Desc.TCons (`Dim, Tm.B (_, tele)), tm :: tms ->
        let r = eval_dim env tm in
        let tyenv = Env.extend_cell tyenv @@ `Dim r in
        let acc = acc #< (`Dim r) in
        go acc tyenv tele tms
      | _ ->
        raise @@ E MalformedConstructorArguments
    in
    go Emp tyenv constr args

  and eval_cmd rel env (hd, sp) =
    let folder hd frm =
      let frm = eval_frame rel env frm in
      Con.plug rel ~rigid:false frm hd
    in
    List.fold_left folder (eval_head rel env hd) sp

  and eval_frame rel env =
    function
    | Tm.Fst -> Fst

    | Tm.Snd -> Snd

    | Tm.FunApp t ->
      let v = Val.make @@ eval rel env t in
      FunApp (TypedVal.make v)

    | Tm.ExtApp trs ->
      let rs = List.map (eval_dim env) trs in
      ExtApp rs

    | Tm.RestrictForce ->
      RestrictForce

    | Tm.VProj info ->
      VProj
        {r = eval_dim env info.r;
         func = TypedVal.make @@ Val.make @@ eval rel env info.func}

    | Tm.Cap info ->
      Cap
        {r = eval_dim env info.r;
         r' = eval_dim env info.r';
         ty = Val.make @@ eval rel env info.ty;
         sys = eval_bnd_sys rel env info.sys}

    | Tm.Elim info ->
      let mot = Clo {env; bnd = info.mot} in
      let params =
        flip List.map info.params @@ fun t ->
        Cell.lazy_con @@ lazy begin eval rel env t end
      in
      let clauses =
        flip List.map info.clauses @@ fun (lbl, bnd) ->
        lbl, NClo {env; bnd}
      in
      Elim {lbl = info.dlbl; mot; params; clauses}

  and eval_bnd rel env =
    function
    | Tm.B (nm, tm) ->
      let x = Name.named nm in
      let env = Env.extend_cell env @@ `Dim (`Atom x) in
      Abs (x, eval rel env tm)

  and eval_head rel env =
    function
    | Tm.Down info ->
      eval rel env info.tm

    | Tm.DownX _ ->
      raise @@ E ExpectedTypeAnnotation

    | Tm.Coe info ->
      let r = eval_dim env info.r in
      let r' = eval_dim env info.r' in
      let abs = eval_bnd rel env info.ty  in
      let cap = Val.make @@ eval rel env info.tm in
      Con.make_coe rel r r' ~abs cap

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
        | `Val v -> LazyVal.unleash v
        | `Dim _ -> raise @@ E UnexpectedDimension
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
        | _ -> raise @@ E GlobalVariableWrongKind
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
        | _ -> raise @@ E GlobalVariableWrongKind
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

  and eval_bnd_face rel env (tr, tr', bnd) =
    let r = eval_dim env tr in
    let r' = eval_dim env tr' in
    match Rel.equate r r' rel with
    | `Changed rel ->
      let env = Env.run rel env in
      let abs = lazy begin eval_bnd rel env bnd end in
      Some (r, r', LazyValAbs.make_from_lazy abs)
    | `Same ->
      let abs = lazy begin eval_bnd rel env bnd end in
      Some (r, r', LazyValAbs.make_from_lazy abs)
    | `Inconsistent ->
      None

  and eval_bnd_sys rel env =
    Option.filter_map (eval_bnd_face rel env)

  and eval_tm_face rel env (tr, tr', tm) =
    let r = eval_dim env tr in
    let r' = eval_dim env tr' in
    match Rel.equate r r' rel with
    | `Changed rel ->
      let env = Env.run rel env in
      let v = lazy begin eval rel env tm end in
      Some (r, r', LazyVal.make_from_lazy v)
    | `Same ->
      let v = lazy begin eval rel env tm end in
      Some (r, r', LazyVal.make_from_lazy v)
    | `Inconsistent ->
      None

  and eval_tm_face_ rel env (tr, tr', tm) =
    let r = eval_dim env tr in
    let r' = eval_dim env tr' in
    match Rel.equate r r' rel with
    | `Changed rel ->
      let env = Env.run rel env in
      let v = lazy begin eval rel env tm end in
      (r, r', LazyVal.make_from_lazy v)
    | `Same ->
      let v = lazy begin eval rel env tm end in
      (r, r', LazyVal.make_from_lazy v)
    | `Inconsistent ->
      (r, r', LazyVal.make FortyTwo)

  and eval_tm_sys rel env =
    Option.filter_map (eval_tm_face rel env)
end

(** Everything in dim is a value. *)
and Dim : Domain with type t = dim =
struct
  type t = dim

  let pp = I.pp

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


  let pp fmt _ =
    Format.fprintf fmt "<clo>"

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

  let pp fmt _ =
    Format.fprintf fmt "<nclo>"

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

  let pp fmt _ =
    Format.fprintf fmt "<ext-clo>"

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
and Cell : sig
  include Domain with type t = cell

  val dim : dim -> cell
  val con : con -> cell
  val value : value -> cell
  val lazy_con : con Lazy.t -> cell
end=
struct
  type t = cell

  let dim r = `Dim r
  let con el = `Val (LazyVal.make el)
  let lazy_con el = `Val (LazyVal.make_from_lazy el)
  let value v = `Val (LazyVal.make_from_delayed v)

  let pp fmt =
    function
    | `Dim r -> Format.fprintf fmt "@[<hov1>(dim@ %a)@]" Dim.pp r
    | `Val v -> Format.fprintf fmt "@[<hov1>(val@ %a)@]" LazyVal.pp v

  let swap pi =
    function
    | `Dim d -> `Dim (Dim.swap pi d)
    | `Val v -> `Val (LazyVal.swap pi v)

  let subst r x =
    function
    | `Dim d -> `Dim (Dim.subst r x d)
    | `Val v -> `Val (LazyVal.subst r x v)

  let run rel =
    function
    | `Dim _ as c -> c
    | `Val v -> `Val (LazyVal.run rel v)
end

and ConstrCell :
sig
  include Domain with type t = constr_cell
  val dim : dim -> t
  val const : con -> t
  val rec_ : constr_rec_spec -> con -> t

  val to_cell : t -> cell
end =
struct
  type t = constr_cell

  let dim r = `Dim r
  let const el = `Const (Val.make el)
  let rec_ rspec el = `Rec (rspec, Val.make el)

  let to_cell : t -> cell =
    function
    | `Dim r -> Cell.dim r
    | `Rec (_, el) -> Cell.value el
    | `Const el -> Cell.value el

  let pp fmt _ =
    Format.fprintf fmt "<constr-cell>"

  let swap pi : t -> t =
    function
    | `Const v -> `Const (Val.swap pi v)
    | `Rec (`Self, v) -> `Rec (`Self, Val.swap pi v)
    | `Dim d -> `Dim (Dim.swap pi d)

  let subst r x =
    function
    | `Const v -> `Const (Val.subst r x v)
    | `Rec (`Self, v) -> `Rec (`Self, Val.subst r x v)
    | `Dim d -> `Dim (Dim.subst r x d)

  let run rel =
    function
    | `Const v -> `Const (Val.run rel v)
    | `Rec (`Self, v) -> `Rec (`Self, Val.run rel v)
    | `Dim _ as c -> c
end

(** An environment is a value if every cell of it is. *)
and Env :
sig
  include Domain with type t = env

  val init : GlobalEnv.t -> env

  val init_isolated : cell list -> env (* Should this take GlobalEnv.t? *)
  val extend_cell : env -> cell -> env
  val extend_cells : env -> cell list -> env
  val lookup_cell_by_index : int -> env -> cell

  val clear_locals : env -> env
end =
struct
  type t = env


  let pp fmt _ =
    Format.fprintf fmt "<env>"

  let swap pi env =
    {env with cells = Bwd.map (Cell.swap pi) env.cells}

  let subst r x env =
    {env with cells = Bwd.map (Cell.subst r x) env.cells}

  let run rel env =
    {env with cells = Bwd.map (Cell.run rel) env.cells}

  let init globals = {globals = globals; cells = Emp}

  let init_isolated cells = {globals = GlobalEnv.emp (); cells = Bwd.from_list cells}

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
  val make_coe : rel -> dim -> dim -> abs:con abs -> value -> con

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

  (* ty and neu are values, but neu might not be rigid *)
  val make_neu : rel -> value -> neutroid -> con

  (** invariant: [args] is [rel]-value, but [sys] might not be rigid *)
  val make_intro : rel -> dlbl:Name.t -> clbl:string -> args:constr_cell list -> sys:con sys -> con

  val make_arr : rel -> value -> value -> con
end =
struct
  module ConFace = Face (Con)
  module ConSys = Sys (Con)
  module ConAbs = AbsPlug (Con)
  module ConAbsFace = Face (ConAbs)
  module ConAbsSys = Sys (ConAbs)
  module ValAbs = AbsPlug (Val)

  type t = con

  let pp fmt =
    function
    | Pi quant ->
      Format.fprintf fmt "@[<hov1>(pi@ %a)@]" Quantifier.pp quant
    | Sg quant ->
      Format.fprintf fmt "@[<hov1>(pi@ %a)@]" Quantifier.pp quant
    | Ext _ ->
      Format.fprintf fmt "<ext>"
    | Restrict _ ->
      Format.fprintf fmt "<restrict>"
    | Lam _ ->
      Format.fprintf fmt "<lam>"
    | Cons _ ->
      Format.fprintf fmt "<ons>"
    | ExtLam nclo ->
      Format.fprintf fmt "@[<hov1>(ext-lam@ %a)@]" NClo.pp nclo
    | RestrictThunk _ ->
      Format.fprintf fmt "<restrict-thunk>"
    | Coe _ ->
      Format.fprintf fmt "<coe>"
    | HCom {r; r'; ty; cap; sys} ->
      Format.fprintf fmt "@[<hov1>(hcom %a %a@ %a@ %a@ %a)@]" Dim.pp r Dim.pp r' HComShape.pp ty Val.pp cap ConAbsSys.pp sys
    | Com _ ->
      Format.fprintf fmt "<com>"
    | GHCom _ ->
      Format.fprintf fmt "<ghcom>"
    | GCom _ ->
      Format.fprintf fmt "<gcom>"
    | Neu {neu; _} ->
      Neutroid.pp fmt neu
    | Data _ ->
      Format.fprintf fmt "<data>"
    | Univ _ ->
      Format.fprintf fmt "<univ>"
    | V {r; ty0; ty1; equiv} ->
      Format.fprintf fmt "@[<hov1>(V %a@ %a@ %a@ %a)@]" Dim.pp r Val.pp ty0 Val.pp ty1 Val.pp equiv
    | VIn {r; el0; el1} ->
      Format.fprintf fmt "@[<hov1>(Vin %a@ %a@ %a)@]" Dim.pp r Val.pp el0 Val.pp el1
    | Box _ ->
      Format.fprintf fmt "<box>"
    | FortyTwo ->
      Format.fprintf fmt "forty-two"
    | _ ->
      Format.fprintf fmt "<con>"

  let make_arr rel ty0 ty1 =
    let env = Env.init_isolated [Cell.value ty1; Cell.value ty0] in
    Syn.eval rel env @@
    Tm.arr (Tm.up @@ Tm.ix 0) (Tm.up @@ Tm.ix 1)

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

    | Data info ->
      Data
        {lbl = info.lbl;
         strict = info.strict;
         params = List.map (Cell.swap pi) info.params;
         constrs = info.constrs}

    | Intro info ->
      Intro
        {dlbl = info.dlbl;
         clbl = info.clbl;
         args = List.map (ConstrCell.swap pi) info.args;
         sys = ConSys.swap pi info.sys}


    | FortyTwo ->
      FortyTwo

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

    | Data info ->
      Data
        {lbl = info.lbl;
         strict = info.strict;
         params = List.map (Cell.subst r x) info.params;
         constrs = info.constrs}

    | Intro info ->
      Intro
        {dlbl = info.dlbl;
         clbl = info.clbl;
         args = List.map (ConstrCell.subst r x) info.args;
         sys = ConSys.subst r x info.sys}

    | FortyTwo ->
      FortyTwo

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
        | exception ConFace.Dead ->
          raise @@ E UnexpectedDeadFace
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
        | exception ConFace.Dead ->
          raise @@ E UnexpectedDeadFace
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
      let neu = Neutroid.run rel info.neu in
      let ty = Val.run rel info.ty in
      make_neu rel ty neu

    | Data info ->
      Data
        {lbl = info.lbl;
         strict = info.strict;
         params = List.map (Cell.run rel) info.params;
         constrs = info.constrs}

    | Intro info ->
      let args = List.map (ConstrCell.run rel) info.args in
      let sys = ConSys.run rel info.sys in
      make_intro rel ~dlbl:info.dlbl ~clbl:info.clbl ~args ~sys

    | FortyTwo ->
      FortyTwo

  and plug rel ~rigid frm hd =
    if rigid then
      rigid_plug rel frm hd
    else
      match Frame.force rel frm ~hd with
      | `Rigid frm -> rigid_plug rel frm hd
      | `Triv c -> c

  and rigid_plug rel frm hd =
    match frm, hd with
    | FunApp arg, Lam clo ->
      Clo.inst rel clo @@ Cell.value @@ TypedVal.drop_ty arg

    | FunApp arg, HCom {r; r'; ty = `Pi quant; cap; sys} ->
      let ty = Clo.inst rel quant.cod @@ Cell.value @@ TypedVal.drop_ty arg in
      let cap = Val.plug rel ~rigid:true frm cap in
      let sys = ConAbsSys.plug rel ~rigid:true frm sys in
      rigid_hcom rel r r' ~ty ~cap ~sys

    | FunApp arg, Coe {r; r'; ty = `Pi abs; cap} ->
      let Abs (x, quantx) = abs in
      let y, pi = Perm.freshen_name x in
      let dom = Abs (x, Val.unleash quantx.dom) in
      let coe_arg s = make_coe rel r' s ~abs:dom @@ TypedVal.drop_ty arg in
      let abs =
        let cod_y = Clo.swap pi quantx.cod in
        let coe_r'y = lazy begin coe_arg @@ `Atom y end in
        Abs (y, Clo.inst rel cod_y @@ Cell.lazy_con coe_r'y)
      in
      let cap = Val.plug rel ~rigid:true (FunApp (TypedVal.make @@ Val.make @@ coe_arg r)) cap in
      rigid_coe rel r r' ~abs cap

    | FunApp _, Com {r; r'; ty; cap; sys} ->
      rigid_plug rel frm @@ expand_rigid_com rel r r' ~abs:(ComShape.to_abs ty) ~cap ~sys

    | FunApp arg, GHCom {r; r'; ty = `Pi quant; cap; sys} ->
      let ty = Clo.inst rel quant.cod @@ Cell.value @@ TypedVal.drop_ty arg in
      let cap = Val.plug rel ~rigid:true frm cap in
      let sys = ConAbsSys.plug rel ~rigid:true frm sys in
      rigid_ghcom rel r r' ~ty ~cap ~sys

    | FunApp _, GCom {r; r'; ty; cap; sys} ->
      rigid_plug rel frm @@ expand_rigid_gcom rel r r' ~abs:(ComShape.to_abs ty) ~cap ~sys

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
      rigid_coe rel r r' ~abs cap

    | Fst, Com {r; r'; ty; cap; sys} ->
      rigid_plug rel frm @@ expand_rigid_com rel r r' ~abs:(ComShape.to_abs ty) ~cap ~sys

    | Fst, GHCom {r; r'; ty = `Sg {dom; _}; cap; sys} ->
      let ty = Val.unleash dom in
      let cap = Val.plug rel ~rigid:true Fst cap in
      let sys = ConAbsSys.plug rel ~rigid:true Fst sys in
      rigid_ghcom rel r r' ~ty ~cap ~sys

    | Fst, GCom {r; r'; ty; cap; sys} ->
      rigid_plug rel frm @@ expand_rigid_gcom rel r r' ~abs:(ComShape.to_abs ty) ~cap ~sys

    | Snd, Cons (_, v1) ->
      Val.unleash v1

    | Snd, HCom ({r; r'; ty = `Sg {dom; cod}; cap; sys} as hcom) ->
      let abs = ConAbs.bind @@ fun y ->
        let hcom_ry_fst =
          lazy begin
            plug rel ~rigid:true Fst (HCom {hcom with r' = y})
          end
        in
        Clo.inst rel cod @@ Cell.lazy_con hcom_ry_fst
      in
      let cap = Val.plug rel ~rigid:true Snd cap in
      let sys = ConAbsSys.plug rel ~rigid:true Snd sys in
      rigid_com rel r r' ~abs ~cap ~sys

    | Snd, Coe ({r; r'; ty = `Sg (Abs (x, {dom = dom_x; cod = cod_x})); cap} as coe) ->
      let abs =
        let y, pi = Perm.freshen_name x in
        let coe_ry_fst = lazy begin plug rel ~rigid:true Fst (Coe {coe with r' = `Atom y}) end in
        let cod_y = Clo.swap pi cod_x in
        let cod_y_coe_ry_fst = Clo.inst rel cod_y @@ Cell.lazy_con coe_ry_fst in
        Abs (y, cod_y_coe_ry_fst)
      in
      let cap = Val.plug rel ~rigid:true Snd cap in
      rigid_coe rel r r' ~abs cap

    | Snd, Com {r; r'; ty; cap; sys} ->
      rigid_plug rel frm @@ expand_rigid_com rel r r' ~abs:(ComShape.to_abs ty) ~cap ~sys

    | Snd, GHCom ({r; r'; ty = `Sg {dom; cod}; cap; sys} as ghcom) ->
      let abs = ConAbs.bind @@ fun y ->
        let ghcom_ry_fst =
          lazy begin
            plug rel ~rigid:true Fst (GHCom {ghcom with r' = y})
          end
        in
        Clo.inst rel cod @@ Cell.lazy_con ghcom_ry_fst
      in
      let cap = Val.plug rel ~rigid:true Snd cap in
      let sys = ConAbsSys.plug rel ~rigid:true Snd sys in
      rigid_gcom rel r r' ~abs ~cap ~sys

    | Snd, GCom {r; r'; ty; cap; sys} ->
      rigid_plug rel frm @@ expand_rigid_gcom rel r r' ~abs:(ComShape.to_abs ty) ~cap ~sys

    | ExtApp rs, ExtLam nclo ->
      NClo.inst rel nclo @@ List.map Cell.dim rs

    | ExtApp rs as frm, HCom {r; r'; ty = `Ext extclo; cap; sys} ->
      let ty, ext_sys =
        let dim_cells = List.map Cell.dim rs in
        ExtClo.inst rel extclo dim_cells
      in
      begin
        match ConSys.force rel ext_sys with
        | ext_sys ->
          let cap = Val.plug rel ~rigid:true frm cap in
          let ext_sys =
            ConAbsSys.foreach_make rel ext_sys @@ fun r r' bdy _ ->
            ConAbs.bind @@ fun _ -> LazyVal.unleash bdy
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
        let dim_cells = List.map Cell.dim rs in
        ExtClo.inst rel_y extclo_y dim_cells
      in
      begin
        match ConSys.force rel sys_y with
        | sys_y ->
          let abs = Abs (y, ty_y) in
          let cap = Val.plug rel ~rigid:true frm cap in
          let sys =
            ConAbsSys.foreach_make rel sys_y @@ fun r r' bdy_y _ ->
            Abs (y, LazyVal.unleash bdy_y)
          in
          rigid_com rel r r' ~abs ~cap ~sys
        | exception ConSys.Triv c_y ->
          run rel @@ subst r' y c_y
      end

    | ExtApp _, Com {r; r'; ty; cap; sys} ->
      rigid_plug rel frm @@ expand_rigid_com rel r r' ~abs:(ComShape.to_abs ty) ~cap ~sys

    | ExtApp rs as frm, GHCom {r; r'; ty = `Ext extclo; cap; sys} ->
      let ty, ext_sys =
        let dim_cells = List.map Cell.dim rs in
        ExtClo.inst rel extclo dim_cells
      in
      begin
        match ConSys.force rel ext_sys with
        | ext_sys ->
          let cap = Val.plug rel ~rigid:true frm cap in
          let ext_sys =
            ConAbsSys.foreach_make rel ext_sys @@ fun r r' bdy _ ->
            ConAbs.bind @@ fun _ -> LazyVal.unleash bdy
          in
          let comp_sys = ConAbsSys.plug rel ~rigid:true frm sys in
          let sys = ext_sys @ comp_sys in
          rigid_hcom rel r r' ~ty ~cap ~sys
        | exception ConSys.Triv c -> c
      end

    | ExtApp _, GCom {r; r'; ty; cap; sys} ->
      rigid_plug rel frm @@ expand_rigid_gcom rel r r' ~abs:(ComShape.to_abs ty) ~cap ~sys

    | RestrictForce, RestrictThunk (r, r', v) ->
      begin
        match Rel.compare r r' rel with
        | `Same -> LazyVal.unleash v
        | _ ->
          raise @@ E InvalidRestrictionProjection
      end

    | VProj _, VIn {el1; _} ->
      Val.unleash el1

    | Cap _, Box {cap; _} ->
      Val.unleash cap

    | Elim elim, Intro intro ->
      let act_on_constr_cell : constr_cell -> _ =
        function
        | `Const v ->
          [Cell.value v]
        | `Rec (`Self, v) ->
          let v_ih = Val.plug rel ~rigid:true frm v in
          [Cell.value v; Cell.value v_ih]
        | `Dim r ->
          [Cell.dim r]
      in
      let cells = ListUtil.flat_map act_on_constr_cell intro.args in
      let nclo = Frame.find_elim_clause intro.clbl elim.clauses in
      NClo.inst rel nclo cells

    | Elim elim, HCom ({ty = `Pos; _} as hcom) ->
      let abs =
        ConAbs.bind @@ fun y ->
        Clo.inst rel elim.mot @@
        Cell.lazy_con @@ lazy begin
          make_fhcom rel hcom.r y ~cap:hcom.cap ~sys:hcom.sys
        end
      in
      let cap = Val.plug rel ~rigid:true frm hcom.cap in
      let sys = ConAbsSys.plug rel ~rigid:true frm hcom.sys in
      rigid_com rel hcom.r hcom.r' ~abs ~cap ~sys

    | _, Neu info ->
      let frm, ty, sys = rigid_plug_ty rel frm info.ty hd in
      begin
        match ConSys.force rel sys with
        | sys ->
          let neu = Neutroid.plug rel ~rigid:true frm info.neu in
          Neu {ty = Val.make ty; neu = {neu with sys = sys @ neu.sys}}
        | exception ConSys.Triv con ->
          con
      end

    | FunApp _, con | Fst, con | Snd, con | ExtApp _, con | RestrictForce, con | VProj _, con | Cap _, con | Elim _, con ->
      raise @@ E (PlugMismatch {frm; con})

  and rigid_plug_ty rel frm ty hd =
    match Val.unleash ty, frm with
    | Pi {dom; cod}, FunApp arg ->
      FunApp {arg with ty = Some dom}, Clo.inst rel cod @@ Cell.value @@ TypedVal.drop_ty arg, []

    | Pi _ as tycon, _ ->
      raise @@ E (PlugTyMismatch {frm; tycon})

    | Sg {dom; _}, Fst ->
      frm, Val.unleash dom, []

    | Sg {cod; _}, Snd ->
      let fst = lazy begin plug rel ~rigid:true Fst hd end in
      frm, Clo.inst rel cod @@ Cell.lazy_con fst, []

    | Sg _ as tycon, _ ->
      raise @@ E (PlugTyMismatch {frm; tycon})

    | Ext extclo, ExtApp rs ->
      let ty, sys = ExtClo.inst rel extclo @@ List.map Cell.dim rs in
      frm, ty, sys

    | Ext _ as tycon, _ ->
      raise @@ E (PlugTyMismatch {frm; tycon})

    | Restrict (r, r', ty), RestrictForce ->
      frm, LazyVal.unleash ty, ConFace.make rel r r' (fun rel -> Con.run rel hd)

    | V {ty0; ty1; _}, VProj info ->
      let arr_ty = make_arr rel ty0 ty1 in
      let face0 =
        ConFace.make rel info.r `Dim0 @@ fun rel ->
        Val.plug_then_unleash rel ~rigid:true (FunApp (TypedVal.make @@ Val.make hd)) info.func.value
      in
      let face1 = ConFace.make rel info.r `Dim1 @@ fun rel -> Con.run rel hd in
      VProj {info with func = {info.func with ty = Some (Val.make arr_ty)}}, Val.unleash ty1, face0 @ face1

    | HCom {ty = `Pos; cap; _}, Cap _ ->
      frm, Val.unleash cap, []

    | Data _, Elim elim ->
      frm, Clo.inst rel elim.mot (Cell.con hd), []

    | Data _ as tycon, _ ->
      raise @@ E (PlugTyMismatch {frm; tycon})

    | tycon, _ ->
      raise @@ E (PlugTyMismatch {frm; tycon})

  and make_coe rel r r' ~abs cap =
    match Rel.compare r r' rel with
    | `Same ->
      Val.unleash cap
    | _ ->
      rigid_coe rel r r' ~abs cap

  and make_neu rel ty neu =
    match Neutroid.force rel neu with
    | neu -> Neu {ty; neu}
    | exception Neutroid.Triv v -> v

  and make_intro rel ~dlbl ~clbl ~args ~sys =
    match ConSys.force rel sys with
    | sys ->
      Intro {dlbl; clbl; args; sys}
    | exception ConSys.Triv con ->
      con

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
    | `Inconsistent -> Val.unleash ty1
    | `Changed rel0 ->
      V {r; ty0 = ty0 rel0; ty1; equiv = equiv rel0}

  and make_vin rel r ~el0 ~el1 =
    match Rel.equate r `Dim0 rel with
    | `Same -> Val.unleash @@ el0 rel
    | `Inconsistent -> Val.unleash el1
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

    | Univ _ | Data _ ->
      HCom {r; r'; ty = `Pos; cap; sys}

    | V ({r = s; _} as info) ->
      let rel0 = Rel.equate' s `Dim0 rel in
      let func = Val.plug rel0 ~rigid:true Fst info.equiv in
      let vproj_frame = VProj {r = s; func = {ty = None; value = func}} in
      let hcom0 r' = make_hcom rel0 r r' ~ty:(Val.unleash info.ty0) ~cap:(Val.run rel0 cap) ~sys:(ConAbsSys.run rel0 sys) in
      let el0 = Val.make @@ hcom0 r' in
      let el1 = Val.make @@
        let cap = Val.plug rel ~rigid:true vproj_frame cap in
        let sys =
          let face0 =
            ConAbsFace.make rel s `Dim0 @@ fun rel0 ->
            ConAbs.bind @@ fun y ->
            let arg0 = FunApp (TypedVal.make @@ Val.make @@ hcom0 y) in
            Val.plug_then_unleash rel0 ~rigid:true arg0 func
          in
          face0 @ ConAbsSys.plug rel ~rigid:true vproj_frame sys
        in
        rigid_hcom rel r r' ~ty:(Val.unleash info.ty1) ~cap ~sys
      in
      VIn {r = s; el0; el1}

    | HCom ({r = s; r' = s'; ty = `Pos; _} as fhcom) ->
      (* [F]: favonia 11.00100100001111110110101010001000100001011. *)

      (* The algorithm is based on the Anders' alternative hcom in [F]. *)

      (* This is essentially C_M in [F]. *)
      let cap_frame =
        Cap
          {r = fhcom.r;
           r' = fhcom.r';
           ty = fhcom.cap;
           sys = fhcom.sys}
      in

      (* This serves as `O` and the diagonal face in [F]
       * for the coherence conditions in `fhcom.sys` and `s=s'`. *)
      let hcom_template rel y_dest ty =
        make_hcom rel r y_dest ~ty
          ~cap:(Val.run rel cap)
          ~sys:(ConAbsSys.run rel sys)
      in

      (* This is `P` in [F]. *)
      let cap = Val.make @@
        let ty = Val.unleash fhcom.cap in
        let cap = Val.plug rel ~rigid:true cap_frame cap in
        let sys =
          let ri_faces = ConAbsSys.plug rel ~rigid:true cap_frame sys in
          let si_faces = ConAbsSys.foreach_make rel fhcom.sys @@ fun si s'i abs rel ->
            let cap_frame = Frame.run rel cap_frame in
            ConAbs.bind @@ fun y ->
            (* XXX FIXME This is not the most efficient code because we know what [cap_frame]
             * will reduce to, but maybe we can afford this? *)
            Con.plug rel ~rigid:true cap_frame @@ hcom_template rel y (LazyValAbs.inst_then_unleash rel abs s')
          in
          let diag =
            ConAbsFace.make rel r r' @@ fun rel ->
            ConAbs.bind @@ fun y ->
            hcom_template rel y (Val.run_then_unleash rel fhcom.cap)
          in
          List.concat [diag; ri_faces; si_faces]
        in
        make_hcom rel r r' ~ty ~cap ~sys
      in
      let sys =
        ConSys.foreach_make rel fhcom.sys @@ fun si s'i abs rel ->
        hcom_template rel r' (LazyValAbs.inst_then_unleash rel abs s')
      in
      Box {r; r'; cap; sys}

    | Neu info ->
      let neu =
        DelayedNeu.make
          {head = NHCom {r; r'; ty = info.neu; cap; sys};
           frames = Emp}
      in
      let neu_sys =
        let cap_face =
          ConFace.make rel r r' @@ fun rel' ->
          Val.run_then_unleash rel' cap
        in
        let tube_faces =
          ConSys.foreach_make rel sys @@ fun s s' abs rel' ->
          LazyValAbs.inst_then_unleash rel' abs r'
        in
        let old_faces =
          ConSys.foreach_make rel info.neu.sys @@ fun s s' bdy rel' ->
          let ty = LazyVal.run_then_unleash rel' bdy in
          let cap = Val.run rel' cap in
          let sys = ConAbsSys.run rel' sys in
          make_hcom rel' r r' ~ty ~cap ~sys
        in
        List.concat [cap_face; tube_faces; old_faces]
      in
      Neu {ty = Val.make ty; neu = {neu; sys = neu_sys}}

    | _ ->
      raise PleaseRaiseProperError


  and rigid_multi_coe rel r r' data_abs clbl (args : constr_cell list) =
    let Abs (x, data_tyx) = data_abs in
    match data_tyx with
    | Data datax ->

      let rec go tyenv tele args : constr_cell list =
        match tele, args with
        | Desc.TNil _, [] -> []
        | Desc.TCons (`Const tty, Tm.B (_, tele)), `Const v :: args ->
          let tyx = Syn.eval rel tyenv tty in
          let coe_hd s =
            let x', pi = Perm.freshen_name x in
            let tyx' = Con.swap pi tyx in
            make_coe rel r s ~abs:(Abs (x', tyx')) v
          in
          let coe_tl =
            let coe_hd_x = coe_hd @@ `Atom x in
            let tyenv = Env.extend_cell tyenv @@ Cell.con coe_hd_x in
            go tyenv tele args
          in
          `Const (Val.make @@ coe_hd r') :: coe_tl
        | Desc.TCons (`Rec Desc.Self, Tm.B (_, tele)), `Rec (`Self, v) :: args ->
          let coe_hd = rigid_coe rel r r' ~abs:data_abs v in
          let tyenv = Env.extend_cell tyenv @@ Cell.con coe_hd in
          let coe_tl = go tyenv tele args in
          `Rec (`Self, Val.make coe_hd) :: coe_tl
        | Desc.TCons (`Dim, Tm.B (_, tele)), `Dim s :: args ->
          let tyenv = Env.extend_cell tyenv @@ Cell.dim s in
          `Dim s :: go tyenv tele args
        | _ ->
          raise PleaseRaiseProperError

      in

      let genv, constrs = datax.constrs in
      let constr = Desc.lookup_constr clbl constrs in
      let tyenv = Env.extend_cells (Env.init genv) datax.params in
      go tyenv constr args

    | _ ->
      raise PleaseRaiseProperError

  and multi_coe rel r r' data_abs clbl args =
    match Rel.equate r r' rel with
    | `Same ->
      args
    | _ ->
      rigid_multi_coe rel r r' data_abs clbl args

  and constr_cell_to_cell : constr_cell -> cell =
    function
    | `Const v -> Cell.value v
    | `Rec (_, v) -> Cell.value v
    | `Dim r -> Cell.dim r

  (* TODO: pass the data-info pre-extracted *)
  (** invariant: the binder in [abs] {b must} be fresh so that we do not have to
      hide the bound variable from [rel] or worry about shadowing. *)
  and rigid_coe_nonstrict_data rel r r' ~abs cap =
    let Abs (x, tyx) = abs in
    match tyx, Val.unleash cap with
    | Data data, Intro intro ->
      let genv, constrs = data.constrs in
      let constr = Desc.lookup_constr intro.clbl constrs in
      let coerced_args s s' = multi_coe rel s s' abs intro.clbl intro.args in
      let args_rr' = coerced_args r r' in
      let tboundary = Desc.Constr.boundary constr in
      let env_ps = Env.extend_cells (Env.init genv) data.params in
      let intro =
        let benv = Env.extend_cells env_ps @@ List.map constr_cell_to_cell args_rr' in
        let sys = Syn.eval_tm_sys rel benv tboundary in
        make_intro rel ~dlbl:data.lbl ~clbl:intro.clbl ~args:(coerced_args r r') ~sys
      in
      begin
        match tboundary with
        | [] -> intro
        | _ ->
          let faces =
            let args_rx = coerced_args r @@ `Atom x in
            let benv = Env.extend_cells env_ps @@ List.map constr_cell_to_cell args_rx in
            Syn.eval_tm_sys rel benv tboundary
          in

          let correction =
            ConAbsSys.foreach_make rel faces @@ fun s s' (el : LazyVal.t) rel_ss' ->
            let elx = make_coe rel_ss' (`Atom x) r' ~abs:(ConAbs.run rel_ss' abs) @@ Val.make (LazyVal.unleash el) in
            let x', pi = Perm.freshen_name x in
            Abs (x', Con.swap pi elx)
          in

          make_fhcom rel r' r ~cap:(Val.make intro) ~sys:correction
      end

    | Data data, Neu info ->
      let neutroid =
        let neu =
          let head = NCoeData {r; r'; ty = abs; cap = info.neu} in
          DelayedNeu.make @@ {head; frames = Emp}
        in
        let sys =
          ConSys.foreach_make rel info.neu.sys @@ fun s s' el rel_ss' ->
          make_coe rel_ss' r r' ~abs:(ConAbs.run rel_ss' abs) @@ Val.make (LazyVal.unleash el)
        in
        {neu; sys}
      in
      Neu {ty = Val.make @@ ConAbs.inst rel abs r'; neu = neutroid}

    | Data _, HCom info ->
      let cap = Val.make @@ rigid_coe rel r r' ~abs info.cap in
      let sys =
        ConAbsSys.foreach_make rel info.sys @@ fun s s' abs' rel_ss' ->
        ConAbs.bind @@ fun y ->
        make_coe rel_ss' r r' ~abs:(ConAbs.run rel_ss' abs) @@
        Val.make @@ LazyValAbs.inst_then_unleash rel_ss' abs' y
      in
      make_fhcom rel info.r info.r' ~cap ~sys

    | _ ->
      raise PleaseRaiseProperError


  (** Invariant: everything is already a value wrt. [rel], and it [r~>r'] is [rel]-rigid. *)
  and rigid_coe rel r r' ~abs cap : con =
    (* TODO: is this safe? why aren't we needing to freshen? *)
    let x, tyx = ConAbs.unbind abs in
    match tyx with
    | Sg quant ->
      Coe {r; r'; ty = `Sg (Abs (x, quant)); cap}

    | Pi quant ->
      Coe {r; r'; ty = `Pi (Abs (x, quant)); cap}

    | Ext extclo ->
      Coe {r; r'; ty = `Ext (Abs (x, extclo)); cap}

    | Univ _ ->
      Val.unleash cap

    | Data info when info.strict || ListUtil.is_nil info.params ->
      Val.unleash cap

    | Data info ->
      rigid_coe_nonstrict_data rel r r' ~abs cap

    | V info ->
      let atom_info_r = match info.r with `Atom x -> x | _ -> raise PleaseRaiseProperError in
      begin
        let rel0 = Rel.equate' info.r `Dim0 rel in
        let rel1 = Rel.equate' info.r `Dim1 rel in
        let abs0 = Abs (x, Val.unleash info.ty0) in
        let abs1 = Abs (x, Val.unleash info.ty1) in
        let func_x = Val.plug rel0 ~rigid:true Fst info.equiv in
        let vproj_frame_x = VProj {r = info.r; func = {ty = None; value = func_x}} in
        match atom_info_r = x with
        | false ->
          let el0 = Val.make @@ make_coe rel0 r r' ~abs:abs0 @@ Val.run rel0 cap in
          let el1 = Val.make @@
            let cap = Val.plug rel ~rigid:true (Frame.run rel @@ Frame.subst r x vproj_frame_x) cap in
            let sys =
              let face0 =
                info.r, `Dim0,
                LazyValAbs.bind @@ fun y ->
                let arg_y = Val.make @@ make_coe rel0 r y ~abs:(ConAbs.run rel0 abs0) @@ Val.run rel0 cap in
                Val.plug_then_unleash rel0 ~rigid:true (FunApp (TypedVal.make arg_y)) info.equiv
              in
              let face1 =
                info.r, `Dim1,
                LazyValAbs.bind @@ fun y ->
                make_coe rel1 r y ~abs:(ConAbs.run rel1 abs1) @@ Val.run rel1 cap
              in
              [face0; face1]
            in
            rigid_com rel r r' ~abs:abs1 ~cap ~sys
          in
          VIn {r = info.r; el0; el1}

        | true ->
          (* `base` is the cap of the hcom in ty1. *)
          let base = (* under rel *)
            let vproj_frame_xr = Frame.run rel @@ Frame.subst r x vproj_frame_x in
            make_coe rel r r' ~abs:abs1 @@ Val.plug rel ~rigid:false vproj_frame_xr cap
          in

          (* The diagonal face for r=r'. *)
          let face_diag =
            ConAbsFace.make rel r r' @@ fun rel ->
            ConAbs.bind @@ fun _ -> Con.run rel base
          in

          (* The face for r=0. *)
          let face0 =
            ConAbsFace.make rel r `Dim0 @@ fun rel ->
            ConAbs.bind @@ fun _ -> Con.run rel base
          in

          (* This is to generate the element in `ty0` and also the face for r'=0. *)
          let fixer_fiber rel =
            Val.make @@ (* rel |= r'=0 *)

            (* the cleaned-up components under r'=0 *)
            let ty0_x0 = Val.run_then_unleash rel @@ Val.subst `Dim0 x info.ty0 in
            let ty1_x0 = Val.run_then_unleash rel @@ Val.subst `Dim0 x info.ty1 in
            let equiv_x0 = Val.run rel @@ Val.subst `Dim0 x info.equiv in
            let base = Con.run rel base in

            (* the equivalence proof under r'=0 *)
            let is_equiv_x0 = Val.plug rel ~rigid:true Snd equiv_x0 in

            let fiber0 =
              Val.plug rel ~rigid:true Fst @@
              Val.plug rel ~rigid:true (FunApp (TypedVal.make @@ Val.make base)) @@
              is_equiv_x0
            in

            (* the type of the fiber at r'=0. *)
            let fiber0_ty =
              let func_x0 = Val.plug_then_unleash rel ~rigid:true Fst equiv_x0 in
              let env = Env.init_isolated [Cell.con base; Cell.con func_x0; Cell.con ty1_x0; Cell.con ty0_x0] in
              let var i = Tm.up @@ Tm.ix i in
              Syn.eval rel env @@ Tm.fiber ~ty0:(var 0) ~ty1:(var 1) ~f:(var 2) ~x:(var 3)
            in

            (* this gives a path from the fiber [fib] to [fiber0 b] at r=r'=0,
             * where [b] is calculated from [fib] as {[ext_apply (do_snd fib) [`Dim1]]}. *)
            let contr_path_at_r0 rel = (* value under r=r'=0 *)
              let b = Con.run rel base in
              let fib =
                Val.make @@
                let lazy_fa = lazy begin Con.run rel base end in
                let env = Env.init_isolated [Cell.con b] in
                let var i = Tm.up @@ Tm.ix i in
                Cons (Val.run rel cap, Val.make @@ Syn.eval rel env (Tm.refl (var 0)))
              in
              Val.plug rel ~rigid:true (FunApp (TypedVal.make fib)) @@
              Val.plug rel ~rigid:true Snd @@
              Val.plug rel ~rigid:true (FunApp (TypedVal.make @@ Val.make b)) @@
              is_equiv_x0
            in

            let sys =
              let face0 =
                ConAbsFace.make rel r `Dim0 @@ fun rel ->
                ConAbs.bind @@ fun w ->
                Val.plug_then_unleash rel ~rigid:true (ExtApp [w]) (contr_path_at_r0 rel)
              in
              let face1 =
                ConAbsFace.make rel r `Dim1 @@ fun rel ->
                ConAbs.bind @@ fun _ ->
                Val.run_then_unleash rel fiber0
              in
              face0 @ face1
            in
            (* hcom whore cap is (fiber0 base), r=0 face is contr0, and r=1 face is constant *)
            make_hcom rel `Dim1 `Dim0 ~ty:fiber0_ty ~cap:fiber0 ~sys
          in

          let el0 rel_r'0 = Val.plug rel_r'0 ~rigid:true Fst (fixer_fiber rel_r'0) in

          let face_front =
            ConAbsFace.make rel r' `Dim0 @@ fun rel ->
            ConAbs.bind @@ fun w ->
            Val.plug_then_unleash rel ~rigid:true (ExtApp [w]) @@
            Val.plug rel ~rigid:true Snd (fixer_fiber rel)
          in

          let el1 = Val.make @@
            make_hcom rel `Dim1 r'
              ~ty:(Val.run_then_unleash rel @@ Val.subst r' x info.ty1)
              ~cap:(Val.make base) ~sys:(List.concat [face0; face_diag; face_front])
          in
          make_vin rel r' ~el0 ~el1
      end

    | HCom ({ty = `Pos; r = s_x; r' = s'_x; _} as fhcom) ->
      (* {b F}: favonia 11.00100100001111110110101010001000100001011.
       * {b SVO}: Part III (airport). *)

      (* anti-shadowing in OCaml. lol *)
      let coe_cap = cap in
      let cap = () in
      let abs = () in

      (* There are two major contexts we are working in:

         1. The ambient context G.
         2. The ambient context with [x], G+x. All components in [fhcom] live in here.

         Shadowing happens all the time so freshening is sometimes needed. *)

      (* this lives in G *)
      let capty_abs = Abs (x, Val.unleash fhcom.cap) in

      (* this lives in G+x*)
      let cap_frame_x = Cap
          {r = fhcom.r;
           r' = fhcom.r';
           ty = fhcom.cap;
           sys = fhcom.sys}
      in

      (* in G *)
      let s_xr = Dim.subst r x s_x in
      let s_xr' = Dim.subst r' x s_x in
      let s'_xr = Dim.subst r x s'_x in
      let s'_xr' = Dim.subst r' x s'_x in

      (* This is O in {b SVO, F}, living in G.

         The purpose of O is to make sure that, when r=r', we can recover the coercee
         after the long journey detailed below.

         @param rel this should be [Rel.equate' r r' rel]
         @param z_dest the destination in the fhcom direction. *)
      let origin rel z_dest =
        let ty = Val.run_then_unleash rel @@ Val.subst r x fhcom.cap in
        let new_cap =
          let cap_frame_xr = Frame.run rel @@ Frame.subst r x cap_frame_x in
          Val.plug rel ~rigid:false cap_frame_xr @@ Val.run rel coe_cap
        in
        let fhcom_sys_rx = ConAbsSys.run rel @@ ConAbsSys.subst r x fhcom.sys in
        let sys =
          ConAbsSys.foreach_make rel fhcom_sys_rx @@ fun sj_xr s'j_xr absj_xr rel ->
          let absj_xr = LazyValAbs.unleash absj_xr in
          ConAbs.bind @@ fun y ->
          make_coe rel y s_xr ~abs:absj_xr @@ Val.make @@
          make_coe rel s'_xr y ~abs:absj_xr @@ Val.run rel coe_cap
        in
        make_hcom rel s'_xr z_dest ~ty ~cap:new_cap ~sys
      in

      (* This corresponds to N in {b F}, representing the coherence conditions enforced by `fhcom.sys`
       * that are apart from `x`. Be careful! The invariant of this function is extremely tricky!
       *
       * This function in general lives in the context G, except the argument [abs_x].
       *
       * @param r'' the intended destination in the coercion direction.
       * @param s'' the intended destination in the composition direction, under r''/x.
       * @param abs_x a prevalue in G+x, representing the face type. It can be just a prevalue.
       * *)
      let recovery_apart_core rel r'' s'' (preabs_x : con abs) : con =
        let inner_coe =
          Val.make @@
          let rel_x = Rel.hide' x rel in
          let inner_abs = Abs (x, ConAbs.inst rel_x preabs_x s'_x) in
          make_coe rel r r'' ~abs:inner_abs @@ Val.run rel coe_cap
        in
        let abs_xr'' = ConAbs.run rel @@ ConAbs.subst r'' x preabs_x in
        make_coe rel (Dim.subst r'' x s'_x) s'' ~abs:abs_xr'' inner_coe
      in

      (* This is the system of N for apart faces *)
      let recovery_apart_sys (r'' : dim) (s'' : dim) : con sys =
        ConSys.foreach_make rel (ConAbsSys.forall x fhcom.sys) @@ fun sj s'j absj_x rel ->
        recovery_apart_core rel r'' s'' (LazyValAbs.unleash absj_x)
      in

      (* This is P in {b F, SVO}, the naive coercion of the cap part of the box within [fhcom.cap].
       * The problem is that we do not have the boundaries of the box, and even if we have,
       * this naive cap will not be the image of the boundaries.
       *
       * This lives in G. *)
      let naively_coerced_cap =
        Val.make @@
        let abs = ConAbs.run rel capty_abs in
        let new_cap = Val.make @@ origin rel s_xr in
        let sys =
          let diag =
            ConAbsSys.forall x @@
            ConAbsFace.make rel s_x s'_x @@ fun rel ->
            ConAbs.bind @@ fun y ->
            make_coe rel r y ~abs:(ConAbs.run rel capty_abs) (Val.run rel coe_cap)
          in
          let apart_faces =
            let y = Name.fresh () in
            let s_y = Dim.subst (`Atom y) x s_x in
            ConAbsSys.foreach_make rel (recovery_apart_sys (`Atom y) s_y) @@ fun _ _ bdy _ -> Abs (y, LazyVal.unleash bdy)
          in
          diag @ apart_faces
        in
        make_gcom rel r r' ~abs ~cap:new_cap ~sys
      in

      (* This is Q in [F, SVO]. This is used to calculate the preimage of the naively coerced cap
       * for the boundaries and the fixed cap.
       *
       * For equations apart from `x`, the recovery_general will coincide with recovery_apart.
       *
       * This lives in G and is under the substitution r'/x in general, except that [abs_x] is in G+x.
       *
       * @param r'' the intended destination in the coercion direction.
       * @param s'' the intended destination in the composition direction, under r''/x.
       * @param abs_x a prevalue in G+x, representing the face type. It can be just a prevalue. *)
      let recovery_general_core rel s'' abs_x =
        let abs_xr' = ConAbs.run rel @@ ConAbs.subst r' x abs_x in
        let cap = Val.run rel naively_coerced_cap in
        let sys =
          let y = Name.fresh () in
          let diag =
            ConAbsFace.make rel r r' @@ fun rel ->
            Abs (y, recovery_apart_core rel r (`Atom y) abs_x)
          in
          let apart_faces =
            ConAbsSys.foreach_make rel (recovery_apart_sys r' (`Atom y)) @@
            fun _ _ bdy _ -> Abs (y, LazyVal.unleash bdy)
          in
          diag @ apart_faces
        in
        make_gcom rel s_xr' s'' ~abs:abs_xr' ~cap ~sys
      in

      (* A system consisting of Q. *)
      let recovery_general_sys rel s'' =
        ListUtil.flat_foreach fhcom.sys @@ fun (sj_x, s'j_x, absj_x) ->
        (* some optimization for apart faces *)
        if I.absent x sj_x && I.absent x s'j_x then
          begin
            ConFace.make rel sj_x s'j_x @@ fun rel ->
            let absj_x = LazyValAbs.unleash absj_x in
            recovery_apart_core rel r' s'' absj_x
          end
        else
          begin
            let sj_xr' = Dim.subst r' x sj_x in
            let s'j_xr' = Dim.subst r' x s'j_x in
            ConFace.make rel sj_xr' s'j_xr' @@ fun rel ->
            let absj_x = LazyValAbs.unleash absj_x in
            recovery_general_core rel s'' absj_x
          end
      in

      (* This is the "cap" part of the final request in [F, SVO].
       *
       * Using Q, the preimages, this is to calculate the final cap based on the naive cap.
       *
       * This lives in G. *)
      let coerced_cap = Val.make @@
        let ty = Val.run_then_unleash rel @@ Val.subst r' x fhcom.cap in
        let cap = naively_coerced_cap in
        let sys =
          let diag =
            ConAbsFace.make rel r r' @@ fun rel ->
            ConAbs.bind @@ fun w ->
            origin rel w
          in
          let fhcom_sys_xr' = ConAbsSys.run rel @@ ConAbsSys.subst r' x fhcom.sys in
          let recovery_faces =
            let y = Name.fresh () in
            ListUtil.flat_foreach2 fhcom_sys_xr' (recovery_general_sys rel (`Atom y)) @@
            fun (sj_xr', s'j_xr', absj_xr') (_, _, bdy) ->
            ConAbsFace.make rel sj_xr' s'j_xr' @@ fun rel ->
            let absj_xr' = LazyValAbs.unleash absj_xr' in
            Abs (y, make_coe rel (`Atom y) s_xr' ~abs:absj_xr' (Val.make @@ LazyVal.unleash bdy))
          in
          diag @ recovery_faces
        in
        make_hcom rel s_xr' s'_xr' ~ty ~cap ~sys
      in

      (* The box, finally! *)
      make_box rel s_xr' s'_xr' ~cap:coerced_cap ~sys:(recovery_general_sys rel s'_xr')

    | Neu info ->
      let neu =
        DelayedNeu.make
          {head = NCoe {r; r'; ty = Abs (x, info.neu); cap};
           frames = Emp}
      in
      let ty = Val.make_then_run rel (Con.subst r' x tyx) in
      let sys =
        let cap_face =
          ConFace.make rel r r' @@ fun rel' ->
          Val.run_then_unleash rel' cap
        in
        let old_faces =
          ConSys.foreach_make rel (ConSys.forall x info.neu.sys) @@ fun s s' bdy rel' ->
          let abs = ConAbs.run rel' @@ Abs (x, LazyVal.unleash bdy) in
          let cap = Val.run rel' cap in
          make_coe rel' r r' ~abs cap
        in
        cap_face @ old_faces
      in
      Neu {ty; neu = {neu; sys}}

    | _ ->
      raise PleaseRaiseProperError

  and expand_rigid_com rel r r' ~abs ~cap ~sys =
    let ty = ConAbs.inst rel abs r' in
    let cap = Val.make @@ make_coe rel r r' ~abs cap in
    let sys =
      ConAbsSys.foreach_make rel sys @@ fun s s' face rel ->
      let (y, bdy_y) = ConAbs.unbind @@ LazyValAbs.unleash face in
      Abs (y, make_coe rel (`Atom y) r' ~abs @@ Val.make bdy_y)
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

    | V _ | HCom {ty = `Pos; _} | Data _ -> expand_rigid_com rel r r' ~abs ~cap ~sys

    | Neu _ -> expand_rigid_com rel r r' ~abs ~cap ~sys (* really too complicated *)

    | _ ->
      raise PleaseRaiseProperError

  and expand_rigid_ghcom rel s s' ~ty ~cap ~sys =
    match sys with
    | [] -> Val.unleash cap
    | (r, r', abs) :: rest ->
      let face rel0 (dim0, dim1) r' = (* [dim0] and [dim1] will be swapped to generate the symmetric case. *)
        let bdy00 rel00 r' = ConAbs.inst rel00 (LazyValAbs.drop_rel abs) r' in
        let bdy01 rel01 r' =
          make_ghcom rel01 r r' ~ty:(Con.run rel01 ty) ~cap:(Val.run rel01 cap) ~sys:(ConAbsSys.run rel01 rest)
        in
        match Rel.equate r' dim0 rel0 with
        | `Same -> bdy00 rel0 r'
        | `Inconsistent -> bdy01 rel0 r'
        | `Changed rel00 ->
          let rel01 = Rel.equate' r' dim1 rel0 in
          let ty = Con.run rel0 ty in
          let cap = Val.run rel0 cap in
          let sys =
            (r', dim0, LazyValAbs.run rel00 abs) ::
            (r', dim1, LazyValAbs.bind @@ bdy01 rel01) ::
            ConAbsSys.run rel0 rest
          in
          make_hcom rel0 r r' ~ty ~cap ~sys
      in
      match Rel.equate r `Dim0 rel with
      | `Same -> face rel (`Dim0, `Dim1) r'
      | `Inconsistent -> face rel (`Dim1, `Dim0) r'
      | `Changed rel0 ->
        let rel1 = Rel.equate' r `Dim1 rel in
        let sys =
          (r, `Dim0, LazyValAbs.bind @@ face rel0 @@ (`Dim0, `Dim1)) ::
          (r, `Dim1, LazyValAbs.bind @@ face rel1 @@ (`Dim1, `Dim0)) :: rest
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
    let cap = Val.make @@ make_coe rel r r' ~abs cap in
    let sys =
      ConAbsSys.foreach_make rel sys @@ fun s s' face rel ->
      let y, bdy_y = ConAbs.unbind @@ LazyValAbs.unleash face in
      Abs (y, make_coe rel (`Atom y) r' ~abs @@ Val.make bdy_y)
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

and LazyValAbs :
sig
  include DelayedDomainPlug
    with type u = con abs
     and type t = con abs Lazy.t Delayed.t
  val bind : (dim -> con) -> t
  val inst_then_unleash : rel -> t -> dim -> con
end =
struct
  module ConAbs = AbsPlug (Con)
  include DelayedLazyPlug (ConAbs)

  let bind gen = make_from_lazy @@ lazy begin ConAbs.bind gen end

  let inst_then_unleash rel abs r = ConAbs.inst rel (drop_rel abs) r
end

(** A [coe_shape] is a value when its component is. *)
and CoeShape :
sig
  include Domain with type t = coe_shape

  val to_abs : t -> con abs
end =
struct
  type t = coe_shape

  let pp fmt _ =
    Format.fprintf fmt "<coe-shape>"

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

  let to_abs =
    function
    | `Pi (Abs (x, quantx)) -> Abs (x, Pi quantx)
    | `Sg (Abs (x, quantx)) -> Abs (x, Sg quantx)
    | `Ext (Abs (x, extclox)) -> Abs (x, Ext extclox)
end

(** A [hcom_shape] is a value when its component is. *)
and HComShape : Domain with type t = hcom_shape =
struct
  type t = hcom_shape
  module Q = Quantifier

  let pp fmt _ =
    Format.fprintf fmt "<hcom-shape>"

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

and ComShape :
sig
  include Domain with type t = com_shape

  val to_abs : t -> con abs
end = CoeShape

(** A [quantifier] is a value when both of its components are. *)
and Quantifier : Domain with type t = quantifier =
struct
  type t = quantifier

  let pp fmt {dom; cod} =
    Format.fprintf fmt "%a@ %a" Val.pp dom Clo.pp cod

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

(* A [neutroid] is a value if the system is value. A [neutroid] is rigid
 * if its system is. *)
and Neutroid :
sig
  include DomainPlug with type t = neutroid

  exception Triv of con

  val force : rel -> t -> t

  (** sys might not be rigid, but ty must be a value *)
  val reflect_head : rel -> ty:value -> head -> con sys -> con
end =
struct
  type t = neutroid

  module ConSys = Sys (Con)
  exception Triv of con

  let pp fmt {neu; sys} =
    match sys with
    | [] -> DelayedNeu.pp fmt neu
    | _ ->
      Format.fprintf fmt "@[<hv1>(%a@ %a)@]"
        DelayedNeu.pp neu
        ConSys.pp sys

  let swap pi {neu; sys} =
    {neu = DelayedNeu.swap pi neu;
     sys = ConSys.swap pi sys}

  let run rel {neu; sys} =
    (* The system needs to be forced first. The invariant is that
     * if [sys] is rigid, it is safe to run neu *)
    let sys = ConSys.run rel sys in
    let neu = DelayedNeu.run rel neu in
    {neu; sys}

  let force rel {neu; sys} =
    let sys =
      try
        ConSys.force rel sys
      with
      | ConSys.Triv v -> raise @@ Triv v
    in
    {neu; sys}

  let subst r x {neu; sys} =
    {neu = DelayedNeu.subst r x neu;
     sys = ConSys.subst r x sys}

  let plug rel ~rigid frm {neu; sys} =
    if rigid then
      {neu = DelayedNeu.plug ~rigid rel frm neu;
       sys = ConSys.plug ~rigid rel frm sys}
    else
      (* even though we can check whether [frm] is really non-rigid,
       * it should be an invariant that the argument [rigid] is always [true]. *)
      raise PleaseRaiseProperError

  let reflect_head rel ~ty head sys =
    match ConSys.run_then_force rel sys with
    | sys -> Neu {ty; neu = {neu = DelayedNeu.make {head; frames = Emp}; sys}}
    | exception (ConSys.Triv con) -> con
end

(** A [neu] is a value if its head and frames are rigid values. *)
and Neu : DomainPlug with type t = neu =
struct
  type t = neu

  let pp fmt {head; frames} =
    match Bwd.to_list frames with
    | [] -> Head.pp fmt head
    | frames ->
      Format.fprintf fmt "@[<hv1>(%a %a)@]"
        Head.pp head
        (Pp.pp_list Frame.pp) frames

  let swap pi neu =
    {head = Head.swap pi neu.head;
     frames = Bwd.map (Frame.swap pi) neu.frames}

  let run rel neu =
    {head = Head.run rel neu.head;
     frames = Bwd.map (Frame.run rel) neu.frames}

  let subst r x neu =
    {head = Head.subst r x neu.head;
     frames = Bwd.map (Frame.subst r x) neu.frames}

  let plug rel ~rigid frm neu =
    if rigid then
      {neu with
       frames = neu.frames #< frm}
    else
      (* even though we can check whether [frm] is really non-rigid,
       * it should be an invariant that the argument [rigid] is always [true]. *)
      raise PleaseRaiseProperError
end

and DelayedNeu : DelayedDomainPlug with type u = neu and type t = neu Delayed.t =
  DelayedPlug (Neu)

(** A [head] is a value if its components are rigid values. *)
and Head : Domain with type t = head =
struct
  type t = head

  module NeutroidAbs = Abs (Neutroid)
  module ConAbs = AbsPlug (Con)
  module ConAbsSys = Sys (ConAbs)

  let pp fmt =
    function
    | Lvl i ->
      Format.fprintf fmt "#%i" i
    | Var var ->
      Name.pp fmt var.name
    | Meta var ->
      Name.pp fmt var.name
    | NCoe ncoe ->
      Format.fprintf fmt "@[<hov1>(ncoe@ %a %a@ %a@ %a)@]" I.pp ncoe.r I.pp ncoe.r' NeutroidAbs.pp ncoe.ty Val.pp ncoe.cap
    | NCoeData _ ->
      Format.fprintf fmt "<ncoe-data>"
    | NHCom _ ->
      Format.fprintf fmt "<nhcom>"

  let swap pi =
    function
    | Lvl _ | Var _ | Meta _ as h -> h
    | NCoe info ->
      NCoe
        {r = Dim.swap pi info.r;
         r' = Dim.swap pi info.r';
         ty = NeutroidAbs.swap pi info.ty;
         cap = Val.swap pi info.cap}

    | NCoeData info ->
      NCoeData
        {r = Dim.swap pi info.r;
         r' = Dim.swap pi info.r';
         ty = ConAbs.swap pi info.ty;
         cap = Neutroid.swap pi info.cap}
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
    | NCoeData info ->
      NCoeData
        {r = Dim.run rel info.r;
         r' = Dim.run rel info.r';
         ty = ConAbs.run rel info.ty;
         cap = Neutroid.run rel info.cap}
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
    | NCoeData info ->
      NCoeData
        {r = Dim.subst r x info.r;
         r' = Dim.subst r x info.r';
         ty = ConAbs.subst r x info.ty;
         cap = Neutroid.subst r x info.cap}
    | NHCom info ->
      NHCom
        {r = Dim.subst r x info.r;
         r' = Dim.subst r x info.r';
         ty = Neutroid.subst r x info.ty;
         cap = Val.subst r x info.cap;
         sys = ConAbsSys.subst r x info.sys}
end

and TypedVal :
sig
  include Domain with type t = typed_value
  val make : value -> t
  val drop_ty : t -> value
end
=
struct
  type t = typed_value

  let pp fmt {value; _} =
    Val.pp fmt value

  let swap pi {ty; value} =
    {ty = Option.map (Val.swap pi) ty;
     value = Val.swap pi value}

  let run rel {ty; value} =
    {ty = Option.map (Val.run rel) ty;
     value = Val.run rel value}

  let subst r x {ty; value} =
    {ty = Option.map (Val.subst r x) ty;
     value = Val.subst r x value}

  let make v = {ty = None; value = v}
  let drop_ty {value = v; _} = v
end

(** A [frame] value might not be rigid. *)
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

  val find_elim_clause : string -> (string * nclo) list -> nclo
end =
struct
  type t = frame

  module ConAbs = AbsPlug (Con)
  module ConAbsSys = Sys (AbsPlug (Con))

  let find_elim_clause lbl clauses =
    let f =
      function
      | (lbl', nclo) when lbl' = lbl -> Some nclo
      | _ -> None
    in
    match ListUtil.find_map_opt f clauses with
    | Some nclo -> nclo
    | None -> raise PleaseRaiseProperError


  let pp fmt =
    function
    | FunApp arg ->
      TypedVal.pp fmt arg
    | Fst ->
      Format.fprintf fmt "fst"
    | Snd ->
      Format.fprintf fmt "snd"
    | ExtApp rs ->
      Format.fprintf fmt "@[<hov1>(extapp@ [%a])@]" (ListUtil.pp "," I.pp) rs
    | RestrictForce ->
      Format.fprintf fmt "restrict-force"
    | VProj {r; func} ->
      Format.fprintf fmt "@[<hov1>(vproj@ %a@ %a)@]" Dim.pp r TypedVal.pp func
    | Cap _ ->
      Format.fprintf fmt "<cap-frame>"
    | Elim _ ->
      Format.fprintf fmt "<elim>"

  let swap pi =
    function
    | FunApp arg ->
      let arg = TypedVal.swap pi arg in
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
         func = TypedVal.swap pi info.func}
    | Cap info ->
      Cap
        {r = Dim.swap pi info.r;
         r' = Dim.swap pi info.r';
         ty = Val.swap pi info.ty;
         sys = ConAbsSys.swap pi info.sys}
    | Elim info ->
      Elim
        {lbl = info.lbl;
         params = List.map (Cell.swap pi) info.params;
         mot = Clo.swap pi info.mot;
         clauses = flip List.map info.clauses @@ fun (lbl, nclo) -> lbl, NClo.swap pi nclo}

  let subst r x =
    function
    | FunApp arg ->
      let arg = TypedVal.subst r x arg in
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
         func = TypedVal.subst r x info.func}
    | Cap info ->
      Cap
        {r = Dim.subst r x info.r;
         r' = Dim.subst r x info.r';
         ty = Val.subst r x info.ty;
         sys = ConAbsSys.subst r x info.sys}
    | Elim info ->
      Elim
        {lbl = info.lbl;
         params = List.map (Cell.subst r x) info.params;
         mot = Clo.subst r x info.mot;
         clauses = flip List.map info.clauses @@ fun (lbl, nclo) -> lbl, NClo.subst r x nclo}

  let run rel =
    function
    | FunApp arg ->
      let arg = TypedVal.run rel arg in
      FunApp arg
    | Fst | Snd | ExtApp _ | RestrictForce as frm ->
      frm
    | VProj info ->
      let r = Dim.run rel info.r in
      let func =
        match Rel.equate' r `Dim0 rel with
        | rel -> TypedVal.run rel info.func
        | exception I.Inconsistent -> TypedVal.make @@ Val.make FortyTwo
      in
      VProj {r; func}
    | Cap info ->
      Cap
        {r = Dim.run rel info.r;
         r' = Dim.run rel info.r';
         ty = Val.run rel info.ty;
         sys = ConAbsSys.run rel info.sys}
    | Elim info ->
      Elim
        {lbl = info.lbl;
         params = List.map (Cell.run rel) info.params;
         mot = Clo.run rel info.mot;
         clauses = flip List.map info.clauses @@ fun (lbl, nclo) -> lbl, NClo.run rel nclo}

  let occur xs =
    function
    (* TODO *)
    | FunApp _ | VProj _ | Cap _ | Elim _ ->
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
    | FunApp _ | Fst | Snd | ExtApp _ | RestrictForce | Elim _ ->
      `Rigid frm
    | VProj {r; func} ->
      begin
        match Rel.compare r `Dim0 rel with
        | `Same -> `Triv (Val.plug_then_unleash rel ~rigid:true (FunApp (TypedVal.make @@ Val.make hd)) (TypedVal.drop_ty func))
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
            `Triv (Con.make_coe rel r' r ~abs @@ Val.make hd)
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

    (** [foreach_make rel sys f = ListUtil.flat_foreach sys (\ (r, r', bdy) -> Face.make rel r r' (f r r' bdy))] *)
    val foreach_make : rel -> 'a sys -> (dim -> dim -> 'a Lazy.t Delayed.t -> rel -> X.t) -> t
  end =
  functor (X : DomainPlug) ->
  struct
    type t = X.t sys
    module Face = Face (X)

    exception Triv = Face.Triv

    let pp fmt =
      Pp.pp_list Face.pp fmt

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

    let plug rel ~rigid frm sys =
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

    let foreach_make rel sys f = ListUtil.flat_foreach sys (fun (r, r', bdy) -> Face.make rel r r' (f r r' bdy))
  end

(** A [face] is a value if equation is consistent and its element is a value.
  * A face value is rigid if the equation is not true. *)
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

    (** [make] makes a possibly non-rigid face value. *)
    val make : rel -> dim -> dim -> (rel -> X.t) -> t list

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

    let pp fmt (r, r', u) =
      Format.fprintf fmt "%a=%a -> %a"
        Dim.pp r
        Dim.pp r'
        DelayedLazyX.pp u

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
      | `Inconsistent -> raise Dead

    let subst r x (s, s', bdy) =
      Dim.subst r x s, Dim.subst r x s',
      DelayedLazyX.subst r x bdy

    let plug rel ~rigid frm (r, r', bdy) =
      match Rel.equate r r' rel with
      | `Same ->
        r, r',
        DelayedLazyX.plug rel ~rigid frm bdy
      | `Changed rel' ->
        r, r',
        let frm' = Frame.run rel' frm in
        DelayedLazyX.plug rel' ~rigid:false frm' bdy
      | `Inconsistent -> raise Dead (* should not happen by the invariant *)

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

    let make rel r r' f =
      match Rel.equate' r r' rel with
      | rel ->
        [r, r', DelayedLazyX.make_from_lazy @@ lazy begin f rel end]
      | exception I.Inconsistent ->
        []

    let run_then_force rel v = force rel (run rel v)
  end

(** [Abs (x, a)] is a [rel]-value if [a] is a [(Rel.hide' x rel)]-value. *)
and Abs : functor (X : Domain) ->
sig
  include Domain with type t = X.t abs

  val bind : (dim -> X.t) -> t
  val unbind : t -> Name.t * X.t

  (** [inst] will give a [rel]-value. The inputs can be non-values. *)
  val inst : rel -> t -> dim -> X.t
end
  =
  functor (X : Domain) ->
  struct
    type t = X.t abs

    let pp fmt (Abs (x, u)) =
      Format.fprintf fmt "@[<hv1>(<%a>@ %a)@]" Name.pp x X.pp u

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

    let bind gen =
      let y = Name.fresh () in
      Abs (y, gen (`Atom y))

    let unbind abs =
      let Abs (x, a_x) = abs in
      let x', pi = Perm.freshen_name x in
      x', X.swap pi a_x

    let inst rel abs r =
      let Abs (x, a_x) = abs in
      let rel_x = Rel.hide' x rel in
      X.run rel_x @@ X.subst r x a_x
  end

and AbsPlug : functor (X : DomainPlug) ->
sig
  include DomainPlug with type t = X.t abs

  val bind : (dim -> X.t) -> t
  val unbind : t -> Name.t * X.t

  (** [inst] will give a [rel]-value. The inputs can be non-values. *)
  val inst : rel -> t -> dim -> X.t
end
  =
  functor (X : DomainPlug) ->
  struct
    include Abs(X)

    let plug rel ~rigid frm abs =
      let Abs (x, a_x) = abs in
      match Frame.occur1 x frm with
      | `No ->
        let rel_x = Rel.hide' x rel in
        let a_x = X.plug rel_x ~rigid frm a_x in
        Abs (x, a_x)
      | `Might ->
        let y, pi = Perm.freshen_name x in
        let rel_y = rel in
        let a_y = X.plug rel_y ~rigid frm @@ X.swap pi a_x in
        Abs (y, a_y)
  end

and DelayedAbsPlug : functor (X : DomainPlug) ->
sig
  include DelayedDomainPlug
    with type u = X.t abs
     and type t = X.t Delayed.t abs

  val bind : (dim -> X.t) -> t

  (** [inst] will give a [rel]-value. The inputs can be non-values. *)
  val inst : rel -> t -> dim -> X.t Delayed.t
end
  =
  functor (X : DomainPlug) ->
  struct
    type u = X.t abs
    include AbsPlug(DelayedPlug(X))

    module DelayedX = DelayedPlug(X)

    let bind gen =
      let y = Name.fresh () in
      Abs (y, Delayed.make (gen (`Atom y)))

    let make (Abs (x, a)) = Abs (x, DelayedX.make a)

    let make_from_lazy (lazy v) = make v

    let make_from_delayed : X.t abs Delayed.t -> DelayedX.t abs =
      Delayed.fold @@ fun rel (Abs (x, c_x)) -> Abs (x, Delayed.make' (Option.map (Rel.hide' x) rel) c_x)

    let unleash (Abs (x, a)) = Abs (x, DelayedX.unleash a)

    let drop_rel (Abs (x, a)) = Abs (x, DelayedX.drop_rel a)

    let run_then_unleash rel (Abs (x, a_x)) =
      let rel_x = Rel.hide' x rel in
      Abs (x, DelayedX.run_then_unleash rel_x a_x)

    let plug_then_unleash rel ~rigid frm v =
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

    let make_from_delayed v = v

    let unleash = Delayed.unleash X.run

    let drop_rel = Delayed.drop_rel

    let pp fmt d =
      X.pp fmt @@ unleash d


    let swap pi =
      Delayed.fold @@ fun rel v ->
      Delayed.make' (Option.map (Perm.fold Rel.swap pi) rel) (X.swap pi v)

    let subst r x v = Delayed.make @@ X.subst r x (unleash v)

    let run rel v = Delayed.with_rel rel v

    let make_then_run rel = Delayed.make' (Some rel)

    let plug rel ~rigid frm v = Delayed.make @@ X.plug rel ~rigid frm (unleash v)

    let run_then_unleash rel v = X.run rel (Delayed.drop_rel v)

    let plug_then_unleash rel ~rigid frm v = X.plug rel ~rigid frm (unleash v)
  end

and DelayedLazyPlug : functor (X : DomainPlug) ->
  DelayedDomainPlug with type u = X.t and type t = X.t Lazy.t Delayed.t =
  functor (X : DomainPlug) ->
  struct
    type u = X.t
    type t = X.t Lazy.t Delayed.t

    module DelayedX = DelayedPlug (X)

    let make v = Delayed.make @@ lazy v

    let make_from_lazy = Delayed.make

    let make_from_delayed v = Delayed.make @@ lazy begin DelayedX.unleash v end

    let unleash v = Lazy.force @@ Delayed.unleash (fun rel v -> lazy begin X.run rel (Lazy.force v) end) v

    let pp fmt v =
      X.pp fmt @@ unleash v

    let drop_rel v = Lazy.force (Delayed.drop_rel v)

    let swap pi =
      Delayed.fold @@ fun rel v ->
      Delayed.make' (Option.map (Perm.fold Rel.swap pi) rel) @@ lazy begin X.swap pi (Lazy.force v) end

    let subst r x v = Delayed.make @@ lazy begin X.subst r x (unleash v) end

    let run rel v = Delayed.with_rel rel v

    let make_then_run rel v = Delayed.make' (Some rel) (lazy v)

    let plug rel ~rigid frm v = Delayed.make @@ lazy begin X.plug rel ~rigid frm (unleash v) end

    let run_then_unleash rel v = X.run rel (drop_rel v)

    let plug_then_unleash rel ~rigid frm v = X.plug rel ~rigid frm (unleash v)
  end

module ConAbs = AbsPlug (Con)
module ConFace = Face (Con)
module NeutroidAbs = Abs (Neutroid)
