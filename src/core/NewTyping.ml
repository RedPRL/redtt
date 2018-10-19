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
  | DimensionOutOfScope
  | InvalidCofibration
  | RestrictionTypeCofibrationMismatch
  | ExpectedTermInFace
  | ExpectedVType

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
  val restrict_ : t -> D.dim -> D.dim -> t
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

  let restrict_ _ _ _ =
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

  module Rst =
  struct
    let body cx r r' tm =
      match Tm.unleash tm with
      | Tm.RestrictThunk (ts, ts', otm) ->
        let s = eval_dim cx ts in
        let s' = eval_dim cx ts' in
        let rel = Cx.rel cx in
        begin
          match D.Rel.compare r s rel, D.Rel.compare r' s' rel with
          | `Same, `Same -> otm
          | _ -> raise @@ E RestrictionTypeCofibrationMismatch
        end


      | Tm.Up cmd ->
        Some (Tm.up @@ cmd @< Tm.RestrictForce)

      | _ ->
        raise PleaseRaiseProperError

    let sys_body cx sys =
      ConSys.plug (Cx.rel cx) D.RestrictForce sys
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
      if not @@ go cofib [] then
        raise @@ E InvalidCofibration

    let check_dim_scope xs =
      function
      | `Atom x when not @@ List.mem x xs ->
        raise @@ E DimensionOutOfScope
      | _ -> ()

    let check_extension xs =
      function
      | [] -> ()
      | cofib ->
        List.iter (fun (r, r') -> List.iter (check_dim_scope xs) [r; r']) cofib;
        check_valid cofib

  end

  let polarity =
    function
    | D.Pi _ | D.Sg _ | D.Ext _ | D.Restrict _ ->
      `Neg
    | D.Univ _ | D.Data _ | D.Neu _ ->
      `Pos
    | _ ->
      raise CanJonHelpMe

  let rec check_boundary cx ty sys el =
    match sys with
    | [] -> ()
    | (r, r', el') :: sys ->
      match Cx.restrict cx r r' with
      | `Changed cx_rr' ->
        let rel_rr' = Cx.rel cx_rr' in
        let ty_rr' = D.Con.run rel_rr' ty in
        let el_rr' = D.Con.run rel_rr' el in
        let _ = Q.equate_con (Cx.qenv cx_rr') rel_rr' ty_rr' el_rr' @@ D.LazyVal.unleash el' in
        check_boundary cx ty sys el

      | `Same ->
        (* Because the adjacency conditions of the system are presupposed, we only need to check this one face. *)
        ignore @@ Q.equate_con (Cx.qenv cx) (Cx.rel cx) ty el @@ D.LazyVal.unleash el'

      | exception I.Inconsistent ->
        check_boundary cx ty sys el



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

    | `Neg (D.Restrict face, sys), _ ->
      let r, r', ty_rr' = face in
      begin
        match Cx.restrict cx r r', Rst.body cx r r' tm with
        | `Changed cx_rr', Some bdy ->
          let sys_bdy = Rst.sys_body cx_rr' sys in
          check_of_ty cx (D.LazyVal.unleash ty_rr') sys_bdy bdy
        | `Same, Some bdy ->
          let sys_bdy = Rst.sys_body cx sys in
          check_of_ty cx (D.LazyVal.unleash ty_rr') sys_bdy bdy
        | exception I.Inconsistent -> ()
        | _ -> raise @@ E ExpectedTermInFace
      end

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

    | Tm.Restrict (tr, tr', otm) ->
      begin
        let r = eval_dim cx tr in
        let r' = eval_dim cx tr' in
        match Cx.restrict cx r r', otm with
        | `Changed cx_rr', Some tm ->
          check_ty cx_rr' kind tm
        | `Same, Some tm ->
          check_ty cx kind tm
        | exception I.Inconsistent ->
          `Const 0 (* power move *)
        | _ ->
          raise @@ E ExpectedTermInFace
      end

    | _ ->
      raise CanJonHelpMe

  and check_tm_sys cx ty sys =
    let rec loop boundary sys =
      match sys with
      | [] -> ()
      | (tr, tr', otm) :: sys ->
        check cx (`Pos `Dim) tr;
        check cx (`Pos `Dim) tr';
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
          raise @@ E ExpectedTermInFace
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

  and synth cx cmd : positive =
    let hd, stk = cmd in
    raise CanJonHelpMe

  and synth_head cx hd =
    raise CanJonHelpMe

  and synth_stack cx vhd ty stk  =
    match ty, stk with
    | _, [] ->
      ty

    | _, Tm.VProj vproj :: stk ->
      let r = eval_dim cx vproj.r in
      begin
        check cx (`Pos `Dim) vproj.r;
        match D.Rel.compare r `Dim0 (Cx.rel cx) with
        | `Same ->
          let _ = check_ty cx `Pre vproj.ty0 in
          let _ = check_ty cx `Pre vproj.ty1 in
          let ty0 = eval cx vproj.ty0 in
          let ty1 = eval cx vproj.ty1 in
          let func_ty = D.Con.make_arr (Cx.rel cx) (D.Val.make ty0) (D.Val.make ty1) in
          check_of_ty cx func_ty [] vproj.func;
          let vfunc = eval cx vproj.func in
          let vhd =
            D.Val.make_from_lazy @@ lazy begin
              D.Con.plug (Cx.rel cx) (D.FunApp (D.TypedVal.make vhd)) vfunc
            end
          in
          (* r must be equal to 0 *)
          synth_stack cx vhd ty1 stk

        | `Apart ->
          (* r must be equal to 1 *)
          synth_stack cx vhd ty stk

        | `Indet ->
          (* must be in V type *)
          match ty with
          | D.V v ->
            let _ = Q.equate_dim (Cx.qenv cx) (Cx.rel cx) v.r r in
            let cx_r0 = Cx.restrict_ cx r `Dim0 in
            let _ = check_ty cx_r0 `Pre vproj.ty0 in
            let _ = check_ty cx_r0 `Pre vproj.ty1 in
            let ty0 = eval cx_r0 vproj.ty0 in
            let ty1 = eval cx_r0 vproj.ty1 in
            let func_ty0 = D.Con.make_arr (Cx.rel cx_r0) (D.Val.make ty0) (D.Val.make ty1) in
            let func_ty1 = D.Con.make_arr (Cx.rel cx_r0) v.ty0 v.ty1 in
            let _ = Q.equate_tycon (Cx.qenv cx_r0) (Cx.rel cx_r0) func_ty0 func_ty1 in
            check_of_ty cx func_ty0 [] vproj.func;
            let vfunc0 = eval cx_r0 vproj.func in
            let vfunc1 = D.Val.plug_then_unleash (Cx.rel cx_r0) D.Fst v.equiv in
            let _ = Q.equate_con (Cx.qenv cx_r0) (Cx.rel cx_r0) func_ty0 vfunc0 vfunc1 in
            let vhd =
              let frm = D.VProj {r; func = {ty = raise CanJonHelpMe; value = raise CanJonHelpMe}} in
              D.Val.plug (Cx.rel cx) frm vhd
            in
            synth_stack cx vhd (D.Val.unleash v.ty1) stk

          | _ ->
            raise @@ E ExpectedVType
      end

    | D.Sg q, Tm.Fst :: stk ->
      let vhd = D.Val.plug (Cx.rel cx) D.Fst vhd in
      let ty = D.Val.unleash q.dom in
      synth_stack cx vhd ty stk

    | D.Sg q, Tm.Snd :: stk ->
      let rel = Cx.rel cx in
      let vhd0 = D.Val.plug rel D.Fst vhd in
      let vhd1 = D.Val.plug rel D.Snd vhd in
      let ty = inst_clo cx q.cod @@ D.Val.unleash vhd0 in
      synth_stack cx vhd1 ty stk

    | _ ->
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
