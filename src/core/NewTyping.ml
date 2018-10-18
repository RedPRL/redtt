open RedBasis open Bwd
open Combinators

module D = NewDomain
module Q = NewQuote
type error =
  | ExpectedDimension
  | UnexpectedState
  | PolarityMismatch
  | UniverseError
  | ExpectedType

exception E of error
exception PleaseRaiseProperError
exception CanJonHelpMe

module type Cx =
sig
  type t
  val rel : t -> NewRestriction.t
  val genv : t -> GlobalEnv.t
  val venv : t -> D.Env.t
  val qenv : t -> Q.QEnv.t

  val extend : t -> ?name:string option -> D.con -> t * D.con
  val extend_dims : t -> ?names:string option list -> t * Name.t list
  val lookup : t -> ?tw:Tm.twin -> int -> D.con

  val restrict : t -> D.dim -> D.dim -> t D.Rel.m
end

module Cx : Cx  =
struct
  type t =
    {rel : NewRestriction.t;
     venv : D.Env.t;
     qenv : Q.QEnv.t;
     hyps : [`Dim | `Ty of D.con] bwd}

  let rel cx = cx.rel
  let genv cx = cx.venv.globals
  let venv cx = cx.venv
  let qenv cx = cx.qenv

  let lookup cx ?(tw = `Only) ix =
    raise CanJonHelpMe

  let extend _ ?name _ =
    raise CanJonHelpMe

  let extend_dims _ ?names =
    raise CanJonHelpMe

  let restrict _ _ _ =
    raise CanJonHelpMe

end


module TC :
sig
  val check_ty : Cx.t -> Kind.t -> Tm.tm -> Lvl.t
  val check_of_ty : Cx.t -> D.con -> D.con D.sys -> Tm.tm -> unit
end =
struct

  type positive = [`El of D.con | `Dim]
  type phase = [`Pos of positive | `Neg of D.con * D.con D.sys]


  let eval cx = D.Syn.eval (Cx.rel cx) (Cx.venv cx)
  let eval_dim cx = D.Syn.eval_dim (Cx.venv cx)

  let inst_clo cx clo v = D.Clo.inst (Cx.rel cx) clo (D.Val (D.LazyVal.make v))


  open Tm.Notation

  module ConSys = D.Sys (D.Con)


  module Sigma =
  struct
    let split tm =
      match Tm.unleash tm with
      | Tm.Cons (tm0, tm1) ->
        tm0, tm1
      | Tm.Up cmd ->
        Tm.up @@ cmd @< Tm.Fst, Tm.up @@ cmd @< Tm.Snd
      | _ ->
        raise PleaseRaiseProperError


    let split_sys cx sys =
      let sys0 = ConSys.plug (Cx.rel cx) D.Fst sys in
      let sys1 = ConSys.plug (Cx.rel cx) D.Snd sys in
      sys0, sys1
  end

  module Pi =
  struct
    let body tm =
      match Tm.unleash tm with
      | Tm.Lam (Tm.B (_, bdy)) ->
        bdy
      | Tm.Up cmd ->
        let wk = Tm.shift 1 in
        let cmd' = Tm.subst_cmd wk cmd in
        let var = Tm.up @@ Tm.ix 0 in
        let frm = Tm.FunApp var in
        Tm.up @@ cmd' @< frm
      | _ ->
        raise PleaseRaiseProperError

    let sys_body cx x sys =
      ConSys.plug (Cx.rel cx) (D.FunApp (D.TypedVal.make (D.Val.make x))) sys

  end

  module Ext =
  struct
    let body cx xs tm =
      match Tm.unleash tm with
      | Tm.ExtLam (Tm.NB (_, bdy)) ->
        bdy
      | Tm.Up cmd ->
        let n = List.length xs in
        let wk = Tm.shift n in
        let trs =
          flip List.map xs @@ fun x ->
          Q.equate_dim (Cx.qenv cx) (Cx.rel cx) x x
        in
        let cmd' = Tm.subst_cmd wk cmd in
        let frm = Tm.ExtApp trs in
        Tm.up @@ cmd' @< frm
      | _ ->
        raise PleaseRaiseProperError

    let sys_body cx xs sys =
      ConSys.plug (Cx.rel cx) (D.ExtApp xs) sys
  end


  module Cofibration :
  sig
    type t = (D.dim * D.dim) list

    val from_sys : Cx.t -> (Tm.tm, 'a) Tm.system -> t

    (** check that an extension type's cofibration is valid *)
    val check_extension : Name.t list -> t -> unit
  end =
  struct
    type t = (D.dim * D.dim) list

    let from_sys cx =
      List.map @@ fun (tr, tr', _) ->
      let env = Cx.venv cx in
      let r = eval_dim cx tr in
      let r' = eval_dim cx tr' in
      r, r'

    (* This is checking whether cofib is valid (forming a non-bipartite graph). *)
    let check_valid (cofib : t) =
      (* the idea is to find an evil assignment (coloring) to make everything false *)
      let assignment = Hashtbl.create 10 in
      let adjacency = Hashtbl.create 20 in
      let rec color x b =
        Hashtbl.add assignment x b;
        let neighbors = Hashtbl.find_all adjacency x in
        let notb = not b in
        List.exists (fun y -> check_color y notb) neighbors
      and check_color x b =
        match Hashtbl.find_opt assignment x with
        | Some b' -> b' != b (* non-bipartite! *)
        | None -> color x b
      in
      let lookup_dim =
        function
        | `Dim0 -> `Assigned false
        | `Dim1 -> `Assigned true
        | `Atom x ->
          match Hashtbl.find_opt assignment x with
          | Some b -> `Assigned b
          | None -> `Atom x
      in
      let rec go eqns atoms_to_check =
        match eqns with
        | [] -> List.exists (fun x -> not (Hashtbl.mem assignment x) && color x true) atoms_to_check
        | (r, r') :: eqns ->
          match lookup_dim r, lookup_dim r' with
          | `Assigned b, `Assigned b' ->
            b = b' || (go[@tailcall]) eqns atoms_to_check
          | `Atom x, `Assigned b | `Assigned b, `Atom x ->
            color x (not b) || (go[@tailcall]) eqns atoms_to_check
          | `Atom x, `Atom y ->
            x = y ||
            begin
              Hashtbl.add adjacency x y;
              Hashtbl.add adjacency y x;
              (go[@tailcall]) eqns (x :: atoms_to_check)
            end
      in
      if go cofib [] then () else failwith "Cofibration.check_valid"

    let check_dim_scope xs =
      function
      | `Dim0 -> ()
      | `Dim1 -> ()
      | `Atom x -> if List.mem x xs then () else failwith "Bad dimension scope"

    let check_extension xs =
      function
      | [] -> ()
      | cofib ->
        List.iter (fun (r, r') -> check_dim_scope xs r; check_dim_scope xs r') cofib;
        check_valid cofib

  end

  let polarity =
    function
    | D.Pi _ | D.Sg _ | D.Ext _ ->
      `Neg
    | D.Univ _ | D.Data _ | D.Neu _ ->
      `Pos
    | _ ->
      raise CanJonHelpMe



  let rec check cx (phase : phase) tm =
    match phase, Tm.unleash tm with
    | `Pos pos, Tm.Up cmd ->
      let pos' = synth cx cmd in
      approx_pos cx pos' pos

    | `Pos `Dim, (Tm.Dim0 | Tm.Dim1) ->
      ()

    | `Pos (`El (D.Univ univ)), _->
      let lvl = check_ty cx univ.kind tm in
      if Lvl.greater lvl univ.lvl then
        raise @@ E UniverseError

    | `Neg (D.Sg q, sys), _ ->
      let tm0, tm1 = Sigma.split tm in
      let sys0, sys1 = Sigma.split_sys cx sys in
      let dom = D.Val.unleash q.dom in
      check_of_ty cx dom sys0 tm0;
      let el0 = eval cx tm0 in
      let cod = inst_clo cx q.cod el0 in
      check_of_ty cx cod sys1 tm1

    | `Neg (D.Pi q, sys), _ ->
      let cx', x = Cx.extend cx @@ D.Val.unleash q.dom in
      let bdy = Pi.body tm in
      let bdy_sys = Pi.sys_body cx x sys in
      let cod = inst_clo cx q.cod x in
      check_of_ty cx cod bdy_sys bdy

    | `Neg (D.Ext eclo, sys), _ ->
      let names = Bwd.to_list @@ D.ExtClo.names eclo in
      let cx', xs = Cx.extend_dims cx ~names in
      let rs = List.map (fun x -> `Atom x) xs in
      let bdy = Ext.body cx rs tm in
      let bdy_sys = Ext.sys_body cx rs sys in
      let cod, cod_sys = D.ExtClo.inst (Cx.rel cx) eclo @@ List.map (fun r -> D.Dim r) rs in
      check_of_ty cx cod (cod_sys @ bdy_sys) bdy

    | _ ->
      raise @@ E UnexpectedState

  (* TODO: we can take from RedPRL the fine-grained subtraction of kinds. Let Favonia do it! *)
  and check_ty cx kind tm : Lvl.t =
    match Tm.unleash tm with
    | Tm.Up cmd ->
      begin
        match synth cx cmd with
        | `El (D.Univ univ) when Kind.lte univ.kind kind ->
          univ.lvl
        | `El (D.Univ univ) ->
          raise @@ E UniverseError
        | _ ->
          raise @@ E ExpectedType
      end

    | Tm.Univ univ ->
      Lvl.shift 1 univ.lvl

    | Tm.Pi (dom, Tm.B (name, cod)) | Tm.Sg (dom, Tm.B (name, cod)) ->
      let lvl0 = check_ty cx kind dom in
      let vdom = eval cx dom in
      let cx', _ = Cx.extend cx ~name vdom in
      check_ty cx' kind cod

    | Tm.Ext ebnd ->
      let Tm.NB (names, (cod, sys)) = ebnd in
      let cx', xs = Cx.extend_dims cx ~names:(Bwd.to_list names) in
      let lvl = check_ty cx' kind cod in
      let vcod = eval cx' cod in
      check_tm_sys cx' vcod sys;
      if Kind.lte kind `Kan then
        Cofibration.check_extension xs @@
        Cofibration.from_sys cx' sys;
      lvl

    | _ ->
      raise CanJonHelpMe

  and check_tm_sys cx ty sys =
    let rec loop boundary sys =
      match sys with
      | [] -> ()
      | (tr, tr', otm) :: sys ->
        check cx (`Pos `Dim) tr;
        check cx (`Pos `Dim) tr';
        let env = Cx.venv cx in
        let r = eval_dim cx tr in
        let r' = eval_dim cx tr' in
        match Cx.restrict cx r r', otm with
        | `Changed cx_rr', Some tm ->
          let rel_rr' = Cx.rel cx_rr' in
          let ty_rr' = D.Con.run rel_rr' ty in
          let boundary_rr' = ConSys.run rel_rr' boundary in
          check_of_ty cx_rr' ty_rr' boundary_rr' tm;
          let el = eval cx_rr' tm in
          loop ((r, r', D.LazyVal.make el) :: boundary) sys
        | `Same, Some tm ->
          check_of_ty cx ty boundary tm;
          let el = eval cx tm in
          loop ((r, r', D.LazyVal.make el) :: boundary) sys
        | exception I.Inconsistent ->
          loop boundary sys
        | _ ->
          raise PleaseRaiseProperError
    in
    loop [] sys


  and check_of_ty cx ty sys tm =
    match polarity ty with
    | `Pos ->
      check cx (`Pos (`El ty)) tm;
      check_boundary cx ty sys @@
      eval cx tm
    | `Neg ->
      check cx (`Neg (ty, sys)) tm

  and check_boundary cx ty sys el =
    raise CanJonHelpMe

  and synth cx cmd : positive =
    raise CanJonHelpMe

  and approx cx ty0 ty1 =
    match polarity ty0, polarity ty1 with
    | `Pos, `Pos ->
      approx_pos cx (`El ty0) (`El ty1)
    | `Neg, `Neg ->
      let cx', _ = Cx.extend cx ty0 in
      let tm = Tm.up @@ Tm.ix 0 in
      check cx (`Neg (ty1, [])) tm
    | _ ->
      raise @@ E PolarityMismatch

  and approx_pos cx (pos0 : positive) (pos1 : positive) =
    match pos0, pos1 with
    | `Dim, `Dim -> ()
    | `El (D.Univ univ0), `El (D.Univ univ1) ->
      if not @@ Lvl.lte univ0.lvl univ1.lvl && Kind.lte univ0.kind univ1.kind then
        raise @@ E UniverseError
    | `El ty0, `El ty1 ->
      ignore @@ Q.equate_tycon (Cx.qenv cx) (Cx.rel cx) ty0 ty1
    | _ ->
      raise @@ E UnexpectedState


end
