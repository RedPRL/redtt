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
  | ExpectedPositiveCommand
  | ExpectedTrueRestrictType
  | KindError
  | UnexpectedDimensionTerm
  | DataParamsLengthMismatch
  | PartialDatatypeDeclaration


let pp_error fmt =
  function
  | ExpectedDimension ->
    Format.fprintf fmt "Expected dimension"
  | UnexpectedState ->
    Format.fprintf fmt "Unexpected state"
  | PolarityMismatch ->
    Format.fprintf fmt "Polarity mismatch"
  | UniverseError ->
    Format.fprintf fmt "Universe error"
  | ExpectedType ->
    Format.fprintf fmt "Expected type"
  | DimensionOutOfScope ->
    Format.fprintf fmt "Dimension out of scope"
  | InvalidCofibration ->
    Format.fprintf fmt "Invalid cofibration"
  | RestrictionTypeCofibrationMismatch ->
    Format.fprintf fmt "Restriction type cofibration mismatch"
  | ExpectedTermInFace ->
    Format.fprintf fmt "Expected term in face"
  | ExpectedVType ->
    Format.fprintf fmt "Expected V type"
  | ExpectedPositiveCommand ->
    Format.fprintf fmt "Expected inferrable term of positive type"
  | ExpectedTrueRestrictType ->
    Format.fprintf fmt "Expected restriction type with true (satisfied) restriction"
  | KindError ->
    Format.fprintf fmt "Universe kind error"
  | UnexpectedDimensionTerm ->
    Format.fprintf fmt "Unexpected dimension term"
  | DataParamsLengthMismatch ->
    Format.fprintf fmt "Datatype parameters were of incorrect length"
  | PartialDatatypeDeclaration ->
    Format.fprintf fmt "Partially declared datatpye cannot be treated as type"

exception E of error

let _ =
  PpExn.install_printer @@ fun fmt ->
  function
  | E err ->
    Format.fprintf fmt "@[<1>%a@]" pp_error err
  | _ ->
    raise PpExn.Unrecognized



exception PleaseRaiseProperError
exception CanJonHelpMe
exception PleaseFillIn

module Cx = NewCx

type positive = [`El of D.con | `Dim]
type phase = [`Pos of positive | `Neg of D.con * D.con D.sys]

let eval cx = D.Syn.eval (Cx.rel cx) (Cx.venv cx)
let eval_dim cx = D.Syn.eval_dim (Cx.venv cx)

let inst_clo cx clo v = D.Clo.inst (Cx.rel cx) clo @@ D.Cell.con v


open Tm.Notation

module ConSys = D.Sys (D.Con)
module ConAbsSys = D.Sys (D.AbsPlug (D.Con))


let quote_ty cx vty =
  Q.equate_tycon (Cx.qenv cx) (Cx.rel cx) vty vty

let quote cx vty el =
  Q.equate_con (Cx.qenv cx) (Cx.rel cx) vty el el


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
        Q.quote_dim (Cx.qenv cx) x
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
      Tm.up @@ cmd @< Tm.RestrictForce

    | _ ->
      raise PleaseRaiseProperError

  let sys_body cx sys =
    ConSys.plug (Cx.rel cx) D.RestrictForce sys
end

module V =
struct
  type t = {r : Tm.tm; tm0 : Tm.tm; tm1 : Tm.tm}
  let split cx ~r ~ty0 ~ty1 ~equiv tm =
    match Tm.unleash tm with
    | Tm.VIn vin ->
      `CheckImage, {r = vin.r; tm0 = vin.tm0; tm1 = vin.tm1}
    | Tm.Up cmd ->
      let cx_r0 = Cx.restrict_ cx r `Dim0 in
      let func = D.Val.plug (Cx.rel cx_r0) D.Fst equiv in
      let func_ty = D.Con.make_arr (Cx.rel cx_r0) (D.Val.make ty0) (D.Val.make ty1) in
      let ty0 = Q.equate_tycon (Cx.qenv cx_r0) (Cx.rel cx_r0) ty0 ty0 in
      let ty1 = Q.equate_tycon (Cx.qenv cx) (Cx.rel cx) ty1 ty1 in
      let tfunc = Q.equate_val (Cx.qenv cx_r0) (Cx.rel cx_r0) func_ty func func in
      let tr = Q.quote_dim (Cx.qenv cx) r in
      let frm = Tm.VProj {r = tr; ty0; ty1; func = tfunc} in
      let vproj = cmd @< frm in
      `NoCheck, {r = tr; tm0 = tm; tm1 = Tm.up vproj}
    | _ ->
      raise PleaseRaiseProperError

  let split_sys cx ~r ~ty0 ~ty1 ~equiv sys =
    let rel = Cx.rel cx in
    let func = D.Val.plug rel D.Fst equiv in
    let frm = D.VProj {r; func = {ty = Some (D.Val.make @@ D.Con.make_arr rel ty0 ty1); value = func}} in
    sys, ConSys.plug rel frm sys

end


module Cofibration :
sig
  type t = (D.dim * D.dim) list

  val from_sys : Cx.t -> (Tm.tm, 'a) Tm.system -> t

  val check_valid : t -> unit

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
  | D.Pi _ | D.Sg _ | D.Ext _ | D.Restrict _ | D.V _ | D.HCom _ ->
    `Neg
  | D.Univ _ | D.Data _ | D.Neu _ ->
    `Pos
  | _ ->
    Format.eprintf "typechecker / polarity ??@.";
    raise CanJonHelpMe

let rec check_boundary cx ty sys el =
  match sys with
  | [] -> ()
  | (r, r', el') :: sys ->
    match Cx.restrict_ cx r r' with
    | cx_rr' ->
      let rel_rr' = Cx.rel cx_rr' in
      let ty_rr' = D.Con.run rel_rr' ty in
      let el_rr' = D.Con.run rel_rr' el in
      let _ = Q.equate_con (Cx.qenv cx_rr') rel_rr' ty_rr' el_rr' @@ D.LazyVal.unleash el' in
      check_boundary cx ty sys el

    | exception I.Inconsistent ->
      check_boundary cx ty sys el



let rec check cx (phase : phase) tm =
  match phase, Tm.unleash tm with
  | _, Tm.Let (cmd, Tm.B (name, body)) ->
    let ty = infer_ty cx cmd in
    let el = eval cx @@ Tm.up cmd in
    let cx' = Cx.extend_def cx ~name ~ty el in
    check cx' phase body

  | _, Tm.VIn vin ->
    check cx (`Pos `Dim) vin.r;
    let r = eval_dim cx vin.r in
    begin
      match D.Rel.compare r `Dim0 (Cx.rel cx) with
      | `Same ->
        (* r = 0 *)
        check cx phase vin.tm0
      | `Apart ->
        (* r = 1 *)
        check cx phase vin.tm1
      | `Indet ->
        (* r = x, ty must be V... *)
        match phase with
        | `Neg (ty, sys) ->
          check_neg cx ty sys tm
        | _ ->
          raise @@ E UnexpectedState
    end

  | _, Tm.Box box ->
    check cx (`Pos `Dim) box.r;
    check cx (`Pos `Dim) box.r';
    let r = eval_dim cx box.r in
    let r' = eval_dim cx box.r' in
    begin
      match D.Rel.compare r r' (Cx.rel cx) with
      | `Same ->
        check cx phase box.cap
      | _ ->
        let rec go =
          function
          | [] ->
            begin
              match phase with
              | `Neg (ty, sys) ->
                check_neg cx ty sys tm
              | _ ->
                raise @@ E UnexpectedState
            end
          | (r, r', tm) :: sys ->
            begin
              check cx (`Pos `Dim) box.r;
              check cx (`Pos `Dim) box.r';
              let r = eval_dim cx box.r in
              let r' = eval_dim cx box.r' in
              match D.Rel.compare r r' (Cx.rel cx) with
              | `Same ->
                check cx phase tm
              | _ ->
                go sys
            end
        in
        go box.sys
    end

  | `Neg (ty, sys), _ ->
    check_neg cx ty sys tm

  | `Pos pos, _ ->
    check_pos cx pos tm

and check_pos cx pos tm =
  match pos, Tm.unleash tm with
  | _, Tm.Up cmd ->
    let pos' = synth cx cmd in
    approx_pos cx pos' pos

  | `Dim, (Tm.Dim0 | Tm.Dim1) ->
    ()

  | `El (D.Univ univ), _->
    let lvl = check_ty_ "univ" cx univ.kind tm in
    if Lvl.greater lvl univ.lvl then
      raise @@ E UniverseError

  | `El (D.Data data), Tm.Intro (dlbl, clbl, params, args) when data.lbl = dlbl->
    let desc = GlobalEnv.lookup_datatype (Cx.genv cx) dlbl in
    check_data_params cx desc.body params;
    let vparams = List.map (fun tm -> D.Cell.con @@ eval cx tm) params in
    let data_ty = eval cx @@ Tm.make @@ Tm.Data {lbl = dlbl; params} in (* this can be optimized *)
    let constr = Desc.lookup_constr clbl @@ Desc.constrs desc in
    check_intro cx data_ty vparams constr args

  | `El (D.Data _), Tm.FHCom _ ->
    Format.eprintf "typechecker/data/fhcom@.";
    raise PleaseFillIn

  | _ ->
    Format.eprintf "typechecker/data/check_pos@.";
    raise PleaseRaiseProperError

and check_neg cx ty sys tm =
  match ty with
  | D.Sg q ->
    let tm0, tm1 = Sigma.split tm in
    let sys0, sys1 = Sigma.split_sys cx sys in
    let dom = D.Val.unleash q.dom in
    check_of_ty_ "sg0" cx dom sys0 tm0;
    let el0 = eval cx tm0 in
    let cod = inst_clo cx q.cod el0 in
    check_of_ty_ "sg1" cx cod sys1 tm1

  | D.Pi q ->
    let cx', x = Cx.extend cx ~name:None @@ D.Val.unleash q.dom in
    let bdy = Pi.body tm in
    let bdy_sys = Pi.sys_body cx x sys in
    let cod = inst_clo cx' q.cod x in
    check_of_ty_ "pi" cx' cod bdy_sys bdy

  | D.Restrict face ->
    let r, r', ty_rr' = face in
    begin
      match Cx.restrict cx r r', Rst.body cx r r' tm with
      | `Changed cx_rr', bdy ->
        let sys_bdy = Rst.sys_body cx_rr' sys in
        check_of_ty_ "rst" cx_rr' (D.LazyVal.unleash ty_rr') sys_bdy bdy
      | `Same, bdy ->
        let sys_bdy = Rst.sys_body cx sys in
        check_of_ty_ "rst" cx (D.LazyVal.unleash ty_rr') sys_bdy bdy
      | exception I.Inconsistent -> ()
    end

  | D.Ext eclo ->
    let names = Bwd.to_list @@ D.ExtClo.names eclo in
    let cx', xs = Cx.extend_dims cx ~names in
    let rs = List.map (fun x -> `Atom x) xs in
    let bdy = Ext.body cx' rs tm in
    let bdy_sys = Ext.sys_body cx' rs sys in
    let cod, cod_sys = D.ExtClo.inst (Cx.rel cx') eclo @@ List.map D.Cell.dim rs in
    check_of_ty_ "ext" cx' cod (cod_sys @ bdy_sys) bdy

  | D.V v ->
    let ty0 = D.Val.unleash v.ty0 in
    let ty1 = D.Val.unleash v.ty1 in
    let mode, vin = V.split cx ~r:v.r ~ty0 ~ty1 ~equiv:v.equiv tm in
    check cx (`Pos `Dim) vin.r;
    let r = eval_dim cx vin.r in
    let _ = Q.equate_dim (Cx.qenv cx) (Cx.rel cx) v.r r in
    let cx_r0 = Cx.restrict_ cx r `Dim0 in

    let vproj_sys0, vproj_sys1 = V.split_sys cx ~r ~ty0:v.ty0 ~ty1:v.ty1 ~equiv:v.equiv sys in

    (* A very powerful Thought is coming here... Carlo and I checked it. *)
    check_of_ty cx_r0 (D.Val.unleash v.ty0) vproj_sys0 vin.tm0;
    let boundary1 =
      match mode with
      | `CheckImage ->
        let func = D.Val.plug (Cx.rel cx_r0) D.Fst v.equiv in
        let el0 = D.Val.make @@ eval cx_r0 vin.tm0 in
        let app = D.Val.plug (Cx.rel cx_r0) (D.FunApp (D.TypedVal.make el0)) func in
        (r, `Dim0, D.LazyVal.make_from_delayed app) :: vproj_sys1
      | `NoCheck -> vproj_sys1
    in
    check_of_ty cx (D.Val.unleash v.ty1) boundary1 vin.tm1

  | D.HCom ({ty = `Pos; _} as fhcom) ->
    (* TODO: unleash a power move like V above *)
    Format.eprintf "typechecker/check element of fhcom@.";
    raise CanJonHelpMe

  | _ ->
    Format.eprintf "typechecker/ty/unhandled@.";
    raise CanJonHelpMe

and check_ty_ str (cx : Cx.t) kind tm =
  Format.eprintf "ty [%s]: %a@." str (Tm.pp (Cx.ppenv cx)) tm;
  check_ty cx kind tm

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
    let lvl0 = check_ty_ "pi/sg" cx kind dom in
    let vdom = eval cx dom in
    let cx', _ = Cx.extend cx ~name vdom in
    check_ty cx' kind cod

  | Tm.Ext ebnd ->
    let Tm.NB (names, (cod, sys)) = ebnd in
    let cx', xs = Cx.extend_dims cx ~names:(Bwd.to_list names) in
    let lvl = check_ty cx' kind cod in
    let vcod = eval cx' cod in
    let _ = check_tm_sys cx' vcod sys in
    if Kind.lte kind `Kan then
      Cofibration.check_extension xs @@
      Cofibration.from_sys cx' sys;
    lvl

  | Tm.Restrict (tr, tr', otm) ->
    (* these aren't kan, are they? *)
    if Kind.lte kind `Kan then
      raise @@ E KindError;
    begin
      let r = eval_dim cx tr in
      let r' = eval_dim cx tr' in
      match Cx.restrict cx r r', otm with
      | `Changed cx_rr', tm ->
        check_ty cx_rr' kind tm
      | `Same, tm ->
        check_ty cx kind tm
      | exception I.Inconsistent ->
        `Const 42 (* power move *)
    end

  | Tm.V v ->
    check cx (`Pos `Dim) v.r;
    let lvl1 = check_ty cx kind v.ty1 in
    let r = eval_dim cx v.r in
    begin
      match Cx.restrict_ cx r `Dim0 with
      | cx_r0 ->
        let lvl0 = check_ty cx_r0 kind v.ty0 in
        let equiv_ty = eval cx_r0 @@ Tm.equiv v.ty0 v.ty1 in
        check_of_ty cx_r0 equiv_ty [] v.equiv;
        Lvl.max lvl0 lvl1
      | exception I.Inconsistent ->
        lvl1
    end

  | Tm.Data {lbl; params} ->
    let desc = GlobalEnv.lookup_datatype (Cx.genv cx) lbl in
    check_data_params cx desc.body params;
    if not @@ Kind.lte desc.kind kind then
      raise @@ E KindError;
    if desc.status = `Partial then
      raise @@ E PartialDatatypeDeclaration;
    desc.lvl

  | Tm.FHCom hcom ->
    check cx (`Pos `Dim) hcom.r;
    check cx (`Pos `Dim) hcom.r';
    let r = eval_dim cx hcom.r in
    let r' = eval_dim cx hcom.r' in
    Cofibration.check_valid @@ Cofibration.from_sys cx hcom.sys;
    let lvl = check_ty cx `Kan hcom.cap in
    let vcap = eval cx hcom.cap in
    let cxx, x = Cx.extend_dim cx ~name:None in
    (* TODO: have a sepcific check_bnd_sys for types *)
    let _ = check_bnd_sys ~cx ~cxx ~x ~r ~ty:(D.Univ {kind = `Kan; lvl}) ~cap:vcap hcom.sys in
    lvl

  | _ ->
    raise CanJonHelpMe

and check_tm_face cx ty sys face =
  let tr, tr', tm = face in
  check cx (`Pos `Dim) tr;
  check cx (`Pos `Dim) tr';
  let r = eval_dim cx tr in
  let r' = eval_dim cx tr' in
  match Cx.restrict cx r r' with
  | `Changed cx_rr' ->
    let rel_rr' = Cx.rel cx_rr' in
    let ty_rr' = D.Con.run rel_rr' ty in
    let boundary_rr' = ConSys.run rel_rr' sys in
    check_of_ty_ "face" cx_rr' ty_rr' boundary_rr' tm;
    let el = eval cx_rr' tm in
    (r, r', D.LazyVal.make el) :: sys
  | `Same ->
    check_of_ty_ "face" cx ty sys tm;
    let el = eval cx tm in
    (r, r', D.LazyVal.make el) :: sys
  | exception I.Inconsistent ->
    sys

and check_data_params cx tele params =
  let rel = Cx.rel cx in
  let rec loop tyenv tele params =
    match tele, params with
    | Desc.TNil _, [] -> ()
    | Desc.TCons (ty, Tm.B (name, tele)), tm :: params ->
      let vty = D.Syn.eval rel tyenv ty in
      check_of_ty cx vty [] tm;
      let el = eval cx tm in
      let tyenv = D.Env.extend_cell tyenv @@ D.Cell.con el in
      loop tyenv tele params
    | _ ->
      raise @@ E DataParamsLengthMismatch
  in
  loop (Cx.venv cx) tele params

and check_intro cx data_ty params constr tms =
  let rel = Cx.rel cx in
  let check_argument tyenv _lbl spec tm =
    match spec with
    | `Const ty ->
      let vty = D.Syn.eval rel tyenv ty in
      check_of_ty cx vty [] tm;
      let el = eval cx tm in
      D.Env.extend_cell tyenv @@ D.Cell.con el
    | `Rec Desc.Self ->
      check_of_ty cx data_ty [] tm;
      let el = eval cx tm in
      D.Env.extend_cell tyenv @@ D.Cell.con el
    | `Dim ->
      check cx (`Pos `Dim) tm;
      let r = eval_dim cx tm in
      D.Env.extend_cell tyenv @@ D.Cell.dim r
  in

  let _ : D.env =
    List.fold_left2
      (fun tyenv (lbl, spec) tm -> check_argument tyenv lbl spec tm)
      (D.Env.extend_cells (D.Env.clear_locals (Cx.venv cx)) params)
      (Desc.Constr.specs constr)
      tms
  in
  ()



(* TODO: check this *)
and check_bnd_face ~cx ~cxx ~x ~r ~ty sys face =
  let ts, ts', (Tm.B (_, tm)) = face in
  check cx (`Pos `Dim) ts;
  check cx (`Pos `Dim) ts';
  let s = eval_dim cx ts in
  let s' = eval_dim cx ts' in
  match Cx.restrict cxx s s' with
  | `Changed cxx_ss' ->
    let rel_ss' = Cx.rel cxx_ss' in
    let ty_ss' = D.Con.run rel_ss' ty in
    let boundary_ss' = ConSys.run rel_ss' sys in
    check_of_ty_ "bface" cxx_ss' ty_ss' boundary_ss' tm;
    let el = eval cxx_ss' tm in
    (s, s', D.LazyVal.make el) :: sys
  | `Same ->
    check_of_ty_ "bface" cxx ty sys tm;
    let el = eval cxx tm in
    (s, s', D.LazyVal.make el) :: sys
  | exception I.Inconsistent ->
    sys

and check_tm_sys cx ty sys =
  List.fold_left (check_tm_face cx ty) [] sys

and check_bnd_sys ~cx ~cxx ~x ~r ~ty ~cap sys =
  let init = [ `Atom x, r, D.LazyVal.make cap ] in
  List.fold_left (check_bnd_face ~cx ~cxx ~x ~r ~ty) init sys

and check_of_ty cx ty sys tm =
  match polarity ty with
  | `Pos ->
    check cx (`Pos (`El ty)) tm;
    check_boundary cx ty sys @@
    eval cx tm
  | `Neg ->
    check cx (`Neg (ty, sys)) tm


and check_of_ty_ debug cx ty sys tm =
  (*   Format.eprintf "%s: %a@." debug (Tm.pp (Cx.ppenv cx)) tm; *)
  check_of_ty cx ty sys tm


and infer_ty cx cmd =
  let hd, stk = cmd in
  match synth_head cx hd with
  | `El ty_in ->
    let vhd = D.Val.make @@ eval cx @@ Tm.up (hd, []) in
    synth_stack cx vhd ty_in stk
  | `Dim ->
    raise @@ E UnexpectedDimensionTerm

and synth cx cmd : positive =
  let hd, stk = cmd in
  match synth_head cx hd, stk with
  | `Dim, [] ->
    `Dim
  | `Dim, _ ->
    raise @@ E ExpectedDimension
  | `El ty_in, _ ->
    let vhd = D.Val.make @@ eval cx @@ Tm.up (hd, []) in
    let ty_out = synth_stack cx vhd ty_in stk in
    match polarity ty_out with
    | `Pos ->
      `El ty_out
    | _ ->
      raise @@ E ExpectedPositiveCommand

and synth_head cx hd =
  match hd with
  | Tm.Ix (ix, _) ->
    Cx.lookup cx ix

  | Tm.Var var ->
    Cx.lookup_const cx ~tw:var.twin ~ushift:var.ushift var.name

  | Tm.Meta meta ->
    Cx.lookup_const cx ~ushift:meta.ushift meta.name

  | Tm.HCom hcom ->
    check cx (`Pos `Dim) hcom.r;
    check cx (`Pos `Dim) hcom.r';
    let r = eval_dim cx hcom.r in
    let r' = eval_dim cx hcom.r' in
    let _ = check_ty_ "hcom" cx `Kan hcom.ty in
    let vty = eval cx hcom.ty in
    Cofibration.check_valid @@ Cofibration.from_sys cx hcom.sys;
    check_of_ty_ "hcom/cap" cx vty [] hcom.cap;
    let vcap = eval cx hcom.cap in
    let cxx, x = Cx.extend_dim cx ~name:None in
    let _ = check_bnd_sys ~cx ~cxx ~x ~r ~ty:vty ~cap:vcap hcom.sys in
    `El vty

  | Tm.Com com ->
    check cx (`Pos `Dim) com.r;
    check cx (`Pos `Dim) com.r';
    let r = eval_dim cx com.r in
    let r' = eval_dim cx com.r' in
    let cxx, x = Cx.extend_dim cx ~name:None in
    let Tm.B (_, ty) = com.ty in
    let _ = check_ty_ "com" cxx `Kan ty in
    let vty = eval cxx ty in
    Cofibration.check_valid @@ Cofibration.from_sys cx com.sys;
    let vty_r = D.Con.run (Cx.rel cx) @@ D.Con.subst r x vty in
    let vty_r' = D.Con.run (Cx.rel cx) @@ D.Con.subst r' x vty in
    check_of_ty_ "com/cap" cx vty_r [] com.cap;
    let vcap = eval cx com.cap in
    let _ = check_bnd_sys ~cx ~cxx ~x ~r:r ~ty:vty ~cap:vcap com.sys in
    `El vty_r'

  | Tm.GHCom ghcom ->
    check cx (`Pos `Dim) ghcom.r;
    check cx (`Pos `Dim) ghcom.r';
    let r = eval_dim cx ghcom.r in
    let r' = eval_dim cx ghcom.r' in
    let _ = check_ty_ "ghcom" cx `Kan ghcom.ty in
    let vty = eval cx ghcom.ty in
    check_of_ty_ "ghcom/cap" cx vty [] ghcom.cap;
    let vcap = eval cx ghcom.cap in
    let cxx, x = Cx.extend_dim cx ~name:None in
    let _ = check_bnd_sys ~cx ~cxx ~x ~r ~ty:vty ~cap:vcap ghcom.sys in
    `El vty

  | Tm.GCom gcom ->
    check cx (`Pos `Dim) gcom.r;
    check cx (`Pos `Dim) gcom.r';
    let r = eval_dim cx gcom.r in
    let r' = eval_dim cx gcom.r' in
    let cxx, x = Cx.extend_dim cx ~name:None in
    let Tm.B (_, ty) = gcom.ty in
    let _ = check_ty_ "gcom" cxx `Kan ty in
    let vty = eval cxx ty in
    let vty_r = D.Con.run (Cx.rel cx) @@ D.Con.subst r x vty in
    let vty_r' = D.Con.run (Cx.rel cx) @@ D.Con.subst r' x vty in
    check_of_ty_ "gcom/cap" cx vty_r [] gcom.cap;
    let vcap = eval cx gcom.cap in
    let _ = check_bnd_sys ~cx ~cxx ~x ~r:r ~ty:vty ~cap:vcap gcom.sys in
    `El vty_r'

  | Tm.Coe coe ->
    check cx (`Pos `Dim) coe.r;
    check cx (`Pos `Dim) coe.r';
    let r = eval_dim cx coe.r in
    let r' = eval_dim cx coe.r' in
    let Tm.B (name, ty) = coe.ty in
    let cxx, x = Cx.extend_dim cx ~name in
    let _ = check_ty cxx `Kan ty in
    let ty_at s =
      let rel = Cx.rel cx in
      let env = Cx.venv cx in
      D.Syn.eval rel (D.Env.extend_cell env @@ D.Cell.dim s) ty
    in
    check_of_ty_ "coe" cx (ty_at r) [] coe.tm;
    `El (ty_at r')

  | Tm.Down {ty; tm} ->
    let _ = check_ty cx `Pre ty in
    let vty = eval cx ty in
    check_of_ty_ "down" cx vty [] tm;
    `El vty

  | Tm.DownX tm ->
    check cx (`Pos `Dim) tm;
    `Dim

and synth_stack cx vhd ty stk  =
  match ty, stk with
  | _, [] ->
    ty

  | _, Tm.VProj vproj :: stk ->
    check cx (`Pos `Dim) vproj.r;
    let r = eval_dim cx vproj.r in
    begin
      match D.Rel.compare r `Dim0 (Cx.rel cx) with
      | `Same ->
        (* r must be equal to 0 *)
        let _ = check_ty cx `Pre vproj.ty0 in
        let _ = check_ty cx `Pre vproj.ty1 in
        let ty0 = eval cx vproj.ty0 in
        let ty1 = eval cx vproj.ty1 in
        let func_ty = D.Con.make_arr (Cx.rel cx) (D.Val.make ty0) (D.Val.make ty1) in
        check_of_ty_ "vproj" cx func_ty [] vproj.func;
        let vfunc = eval cx vproj.func in
        let vhd =
          D.Val.make_from_lazy @@ lazy begin
            D.Con.plug (Cx.rel cx) (D.FunApp (D.TypedVal.make vhd)) vfunc
          end
        in
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
          check_of_ty_ "vproj" cx func_ty0 [] vproj.func;
          let vfunc0 = eval cx_r0 vproj.func in
          let vfunc1 = D.Val.plug_then_unleash (Cx.rel cx_r0) D.Fst v.equiv in
          let _ = Q.equate_con (Cx.qenv cx_r0) (Cx.rel cx_r0) func_ty0 vfunc0 vfunc1 in
          let vhd =
            let frm = D.VProj {r; func = {ty = Some (D.Val.make func_ty0); value = D.Val.make vfunc0}} in
            D.Val.plug (Cx.rel cx) frm vhd
          in
          synth_stack cx vhd (D.Val.unleash v.ty1) stk

        | _ ->
          raise @@ E ExpectedVType
    end

  | _, Tm.Cap _ :: stk ->
    Format.eprintf "typechecker/cap frame@.";
    raise CanJonHelpMe

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

  | D.Pi q, Tm.FunApp tm :: stk ->
    let dom = D.Val.unleash q.dom in
    check_of_ty_ "funapp" cx dom [] tm;
    let arg = eval cx tm in
    let cod = inst_clo cx q.cod arg in
    let frm = D.FunApp (D.TypedVal.make (D.Val.make arg)) in
    let vhd = D.Val.plug (Cx.rel cx) frm vhd in
    synth_stack cx vhd cod stk

  | D.Restrict (r, r', ty), Tm.RestrictForce :: stk ->
    begin
      match D.Rel.compare r r' (Cx.rel cx) with
      | `Same -> synth_stack cx vhd (D.LazyVal.unleash ty) stk
      | _ -> raise @@ E ExpectedTrueRestrictType
    end

  | D.Ext eclo, Tm.ExtApp rs :: stk ->
    let rs =
      flip List.map rs @@ fun r ->
      check cx (`Pos `Dim) r;
      eval_dim cx r
    in
    let ty, _ = D.ExtClo.inst (Cx.rel cx) eclo @@ List.map D.Cell.dim rs in
    let frm = D.ExtApp rs in
    let vhd = D.Val.plug (Cx.rel cx) frm vhd in
    synth_stack cx vhd ty stk

  | D.Data _, Tm.Elim _ :: stk ->
    Format.eprintf "typechecker / data / elim@.";
    raise CanJonHelpMe

  | _, frm :: _ ->
    Format.eprintf "typechecker encountered unimplemented frame: %a@." (Tm.pp_frame Pp.Env.emp) frm;
    raise PleaseFillIn

and approx cx ty0 ty1 =
  match polarity ty0, polarity ty1 with
  | `Pos, `Pos ->
    approx_pos cx (`El ty0) (`El ty1)
  | `Neg, `Neg ->
    let cx', _ = Cx.extend cx ~name:None ty0 in
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


let check_subtype = approx
