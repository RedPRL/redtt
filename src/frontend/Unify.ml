open RedBasis
open RedTT_Core
open Bwd open BwdNotation
open Contextual
open Dev

module D = Domain

module Notation = Monad.Notation (Contextual)
open Notation

type telescope = params

open Tm.Notation

type error =
  | SpineMismatch of Tm.tm Tm.spine * Tm.tm Tm.spine

exception E of error

module Error =
struct
  let pp fmt =
    function
    | SpineMismatch (sp0,sp1) ->
      Format.fprintf fmt
        "@[<v>spine mismatch:@,  @[<v>%a@,%a@]@]"
        (Tm.pp_spine Pp.Env.emp) sp0
        (Tm.pp_spine Pp.Env.emp) sp1

  let _ =
    PpExn.install_printer @@ fun fmt ->
    function
    | E err ->
      pp fmt err
    | _ ->
      raise PpExn.Unrecognized
end

let rec telescope ty : telescope * ty =
  match Tm.unleash ty with
  | Tm.Pi (dom, cod) ->
    let x, codx = Tm.unbind cod in
    let tel, ty = telescope codx in
    (Emp #< (x, `P dom)) <.> tel, ty
  | Tm.CoR (r, r', Some ty) ->
    let x = Name.fresh () in
    let tel, ty = telescope ty in
    (Emp #< (x, `R (r, r'))) <.> tel, ty
  | Tm.Later cod ->
    let x, codx = Tm.unbind cod in
    let tel, ty = telescope codx in
    (Emp #< (x, `Tick)) <.> tel, ty
  | _ ->
    Emp, ty

let rec abstract_tm xs tm =
  match xs with
  | Emp -> tm
  | Snoc (xs, (x, `P _)) ->
    abstract_tm xs @@ Tm.make @@ Tm.Lam (Tm.bind x tm)
  | Snoc (xs, (x, `Def (ty, def))) ->
    abstract_tm xs @@ Tm.unbind_with (Tm.ann ~ty ~tm:def) @@ Tm.bind x tm
  | Snoc (xs, (x, `Tick)) ->
    abstract_tm xs @@ Tm.make @@ Tm.Next (Tm.bind x tm)
  | Snoc (xs, (x, `I)) ->
    let bnd = Tm.NB (Emp #< None, Tm.close_var x 0 tm) in
    abstract_tm xs @@ Tm.make @@ Tm.ExtLam bnd
  | Snoc (xs, (_, `NullaryExt)) ->
    let bnd = Tm.NB (Emp, tm) in
    abstract_tm xs @@ Tm.make @@ Tm.ExtLam bnd
  | Snoc (xs, (_, `R (r, r'))) ->
    abstract_tm xs @@ Tm.make @@ Tm.CoRThunk (r, r', Some tm)
  | Snoc (xs, (_, `KillFromTick _)) ->
    abstract_tm xs tm
  | _ ->
    failwith "abstract_tm"

let rec abstract_ty (gm : telescope) cod =
  match gm with
  | Emp -> cod
  | Snoc (gm, (x, `P dom)) ->
    abstract_ty gm @@ Tm.make @@ Tm.Pi (dom, Tm.bind x cod)
  | Snoc (gm, (x, `Def (dom, def))) ->
    abstract_ty gm @@ Tm.unbind_with (Tm.ann ~ty:dom ~tm:def) @@ Tm.bind x cod
  | Snoc (gm, (_, `R (r, r'))) ->
    abstract_ty gm @@ Tm.make @@ Tm.CoR (r, r', Some cod)
  | Snoc (gm, (x, `I)) ->
    abstract_ty gm @@ Tm.make @@ Tm.Ext (Tm.bind_ext (Emp #< x) cod [])
  | Snoc (gm, (_, `NullaryExt)) ->
    abstract_ty gm @@ Tm.make @@ Tm.Ext (Tm.bind_ext Emp cod [])
  | Snoc (gm, (x, `Tick)) ->
    abstract_ty gm @@ Tm.make @@ Tm.Later (Tm.bind x cod)
  | Snoc (gm, (_, `KillFromTick _)) ->
    abstract_ty gm cod
  | _ ->
    failwith "abstract_ty"

let telescope_to_spine : telescope -> tm Tm.spine =
  Bwd.flat_map @@ fun (x, param) ->
  match param with
  | `I ->
    [Tm.ExtApp [Tm.up @@ Tm.var x]]
  | `NullaryExt ->
    [Tm.ExtApp []]
  | `P _ ->
    [Tm.FunApp (Tm.up @@ Tm.var x)]
  | `Def _ ->
    []
  | `SelfArg _ ->
    (* ??? *)
    [Tm.FunApp (Tm.up @@ Tm.var x)]
  | `Tw _ ->
    [Tm.FunApp (Tm.up @@ Tm.var x)]
  | `R _ ->
    [Tm.CoRForce]
  | `Tick ->
    [Tm.Prev (Tm.up @@ Tm.var x)]
  | `KillFromTick _ ->
    []

let push_hole tag gm ty =
  let alpha = Name.fresh () in
  pushl @@ E (alpha, abstract_ty gm ty, Hole tag) >>
  let hd = Tm.Meta {name = alpha; ushift = 0} in
  let sp = telescope_to_spine gm in
  ret (hd, sp)

let hole tag gm ty f =
  push_hole tag gm ty >>= fun cmd ->
  f cmd >>= fun r ->
  go_left >>
  ret r

let define gm alpha opacity ~ty tm =
  let ty' = abstract_ty gm ty in
  let tm' = abstract_tm gm tm in
  check ~ty:ty' tm' >>= function
  | `Exn exn ->
    raise exn
  | `Ok ->
    begin
      if opacity = `Transparent then push_update alpha else ret ()
    end >>
    pushr @@ E (alpha, ty', Defn (opacity, tm'))

(* This is a crappy version of occurs check, not distingiushing between strong rigid and weak rigid contexts.
   Later on, we can improve it. *)
let occurs_check alpha tm =
  Occurs.Set.mem alpha @@
  Tm.free `Metas tm


(* TODO: move to some code dumping ground, perhaps the basis *)
let rec opt_traverse f xs =
  match xs with
  | [] -> Some []
  | x::xs ->
    match f x with
    | Some y -> Option.map (fun ys -> y :: ys) @@ opt_traverse f xs
    | None -> None

let to_var t =
  match Tm.unleash @@ Tm.eta_contract t with
  | Tm.Up (Tm.Var {name; _}, Emp) ->
    Some name
  | _ ->
    (* Format.eprintf "to_var: %a@.@." (Tm.pp Pp.Env.emp) t; *)
    None


let rec spine_to_tele sp =
  match sp with
  | Emp -> Some Emp
  | Snoc (sp, Tm.FunApp t) ->
    begin
      match to_var t with
      | Some x ->
        Option.map (fun xs -> xs #< (x, `P ())) @@ spine_to_tele sp
      | None ->
        None
    end
  | Snoc (sp, Tm.ExtApp ts) ->
    begin
      match opt_traverse to_var ts with
      | Some xs ->
        Option.map (fun ys -> ys <>< match xs with [] -> [(Name.fresh (), `NullaryExt)] | _ -> List.map (fun x -> (x, `I)) xs) @@ spine_to_tele sp
      | None ->
        None
    end
  | _ -> None

let linear_on t tele =
  let fvs = Tm.free `Vars t in
  let rec occurs_in x xs =
    match xs with
    | Emp -> false
    | Snoc (xs, (y, _)) -> if x = y then true else occurs_in x xs
  in

  let rec go xs =
    match xs with
    | Emp -> true
    | Snoc (xs, (x, `P _)) ->
      not (occurs_in x xs && Occurs.Set.mem x fvs) && go xs
    | Snoc (xs, (x, `I)) ->
      not (occurs_in x xs && Occurs.Set.mem x fvs) && go xs
    | Snoc (xs, (_, `NullaryExt)) ->
      go xs
    | Snoc (_, _) ->
      failwith "linear_on"
  in go tele

let invert alpha ty sp t =
  if occurs_check alpha t then
    failwith "occurs check"
  else (* alpha does not occur in t *)
    match spine_to_tele sp with
    | Some xs when linear_on t xs ->
      begin
        let lam_tm = abstract_tm xs t in
        local (fun _ -> Emp) begin
          check ~ty lam_tm
        end >>= function
        | `Ok ->
          ret @@ Some lam_tm
        | `Exn exn ->
          ret None
      end
    | _ ->
      ret None

let try_invert q ty =
  match Tm.unleash q.tm0 with
  | Tm.Up (Meta {name = alpha; ushift = 0}, sp) ->
    begin
      invert alpha ty sp q.tm1 >>= function
      | None ->
        ret false
      | Some t ->
        active (Unify q) >>
        define Emp alpha `Transparent ~ty t >>
        ret true
    end
  | _ ->
    failwith "try_invert"

let rec flex_term ~deps q =
  match Tm.unleash q.tm0 with
  | Tm.Up (Meta {name = alpha; ushift = 0}, _) ->
    ask <<@> Bwd.map snd >>= fun gm ->
    begin
      popl >>= function
      | E (beta, _, Hole `Rigid) as e when alpha = beta ->
        pushls (e :: deps) >>
        block @@ Unify q

      | E (beta, _, Guess _) as e when alpha = beta ->
        pushls (e :: deps) >>
        block @@ Unify q

      | E (beta, _, Hole _) as e when alpha = beta && Occurs.Set.mem alpha @@ Entries.free `Metas deps ->
        (* Format.eprintf "flex_term/alpha=beta: @[<1>%a@]@." Equation.pp q; *)
        pushls (e :: deps) >>
        block @@ Unify q

      | E (beta, ty, Hole _) as e when alpha = beta ->
        (* Format.eprintf "flex_term/alpha=beta/2: @[<1>%a@]@." Equation.pp q; *)
        pushls deps >>
        try_invert q ty <||
        begin
          (* Format.eprintf "flex_term failed to invert.@."; *)
          block @@ Unify q >>
          pushl e
        end

      | (E (beta, _, Hole _) | E (beta, _, Guess _)) as e
        when
          Occurs.Set.mem beta (Params.free `Metas gm)
          || Occurs.Set.mem beta (Entries.free `Metas deps)
          || Occurs.Set.mem beta (Equation.free `Metas q)
        ->
        (* Format.eprintf "flex_term/3: @[<1>%a@]@." Equation.pp q; *)
        flex_term ~deps:(e :: deps) q

      | e ->
        (* Format.eprintf "flex_term/else: @[<1>%a@] --------- @[<1>%a@]@." Name.pp alpha Entry.pp e; *)
        pushr e >>
        flex_term ~deps q
    end
  | _ -> failwith "flex_term"


let rec flex_flex_diff ~deps q =
  match Tm.unleash q.tm0, Tm.unleash q.tm1 with
  | Tm.Up (Tm.Meta {name = alpha0; ushift = 0}, _), Tm.Up (Tm.Meta {name = alpha1; ushift = 0}, _) ->
    ask <<@> Bwd.map snd >>= fun gm ->
    begin
      popl >>= function
      | E (gamma, _, Hole `Rigid) as e when (alpha0 = gamma || alpha1 = gamma) ->
        pushls @@ e :: deps >>
        block @@ Unify q

      | E (gamma, _, Guess _) as e when (alpha0 = gamma || alpha1 = gamma) ->
        pushls @@ e :: deps >>
        block @@ Unify q

      | E (gamma, _, Hole `Flex) as e
        when
          (alpha0 = gamma || alpha1 = gamma)
          && Occurs.Set.mem gamma @@ Entries.free `Metas deps
        ->
        (* Format.eprintf "flex_flex_diff / popl / 1: %a %a at %a@." Name.pp alpha0 Name.pp alpha1 Name.pp gamma; *)
        pushls @@ e :: deps >>
        block @@ Unify q

      | (E (gamma, ty, Hole _) | E (gamma, ty, Guess _)) as e when gamma = alpha0 ->
        (* Format.eprintf "flex_flex_diff / popl / 2: %a %a at %a@." Name.pp alpha0 Name.pp alpha1 Name.pp gamma; *)
        pushls deps >>
        try_invert q ty <||
        flex_term [e] (Equation.sym q)

      | (E (gamma, _, Hole _) | E (gamma, _, Guess _)) as e
        when
          Occurs.Set.mem gamma @@ Params.free `Metas gm
          || Occurs.Set.mem gamma @@ Entries.free `Metas deps
          || Occurs.Set.mem gamma @@ Equation.free `Metas q
        ->
        (* Format.eprintf "flex_flex_diff / popl / 3: %a %a at %a@." Name.pp alpha0 Name.pp alpha1 Name.pp gamma; *)
        flex_flex_diff ~deps:(e :: deps) q

      | e ->
        (* Format.eprintf "flex_flex_diff / popl / 4: %a %a at @[%a@]@.@." Name.pp alpha0 Name.pp alpha1 Entry.pp e; *)
        pushr e >>
        flex_flex_diff ~deps q
    end

  | _ ->
    failwith "flex_flex_diff"

let rec intersect tele sp0 sp1 =
  match tele, sp0, sp1 with
  | Emp, Emp, Emp ->
    Some Emp
  | Snoc (tele, (z, ty)), Snoc (sp0, Tm.FunApp t0), Snoc (sp1, Tm.FunApp t1) ->
    begin
      match intersect tele sp0 sp1, to_var t0, to_var t1 with
      | Some tele', Some x, Some y ->
        if x = y then Some (tele' #< (z, ty)) else Some tele'
      | _ -> None
    end
  | _ ->
    None

type instantiation = Name.t * ty * (tm Tm.cmd -> tm)

let rec instantiate (inst : instantiation) =
  let alpha, ty, f = inst in
  popl >>= function
  | E (beta, ty', Hole `Flex) when alpha = beta ->
    hole `Flex Emp ty @@ fun cmd ->
    define Emp beta `Transparent ~ty:ty' @@ f cmd
  | e ->
    pushr e >>
    instantiate inst

let flex_flex_same q =
  let alpha, sp0 = q.tm0 in
  let sp1 = q.tm1 in
  lookup_meta alpha >>= fun (ty_alpha, _) ->
  let tele, cod = telescope ty_alpha in
  match intersect tele sp0 sp1 with
  | Some tele' ->
    let f (hd, sp) =
      abstract_tm tele @@
      let sp' = telescope_to_spine tele in
      Tm.up (hd, sp <.> sp')
    in
    instantiate (alpha, abstract_ty tele' cod, f)
  | None ->
    block @@ Unify
      {q with
       tm0 = Tm.up (Tm.Meta {name = alpha; ushift = 0}, sp0);
       tm1 = Tm.up (Tm.Meta {name = alpha; ushift = 0}, sp1)}

let try_prune _q =
  (* TODO: implement pruning *)
  ret false


(* This is all so horrible because we don't have hereditary-substitution-style operations
   directly on the syntax. So we have to factor through evaluation and quotation all the time.

   While checking conversion is most convenient with NBE, it seems that elaboration and
   unification would be better served by a purely syntactic approach based on hereditary
   substitution. *)

let evaluator =
  base_cx >>= fun cx ->
  ret (cx, Cx.evaluator cx)

let inst_ty_bnd bnd (rec_spec, arg) =
  base_cx >>= fun cx ->
  let Tm.B (nm, tm) = bnd in
  let varg = Cx.eval cx arg in
  let lcx = Cx.def cx ~nm ~ty:rec_spec ~el:varg in
  ret @@ Cx.quote_ty cx @@ Cx.eval lcx tm

let eval tm =
  base_cx >>= fun cx ->
  ret @@ Cx.eval cx tm


let inst_bnd (ty_clo, tm_bnd) (rec_spec, arg) =
  evaluator >>= fun (cx, (module V)) ->
  let Tm.B (nm, tm) = tm_bnd in
  let varg = Cx.eval cx arg in
  let lcx = Cx.def cx ~nm ~ty:rec_spec ~el:varg in
  let vty = V.inst_clo ty_clo varg in
  ret @@ Cx.quote cx ~ty:vty @@ Cx.eval lcx tm

let plug (ty, tm) frame =
  base_cx >>= fun cx ->
  let (module V) = Cx.evaluator cx in

  match Tm.unleash tm, frame with
  | Tm.Up cmd, _ ->
    ret @@ Tm.up @@ cmd @< frame
  | Tm.Lam bnd, Tm.FunApp arg ->
    let dom, cod = V.unleash_pi ty in
    inst_bnd (cod, bnd) (dom, arg)
  | Tm.ExtLam _, Tm.ExtApp args ->
    let vargs = List.map (Cx.eval_dim cx) args in
    let ty, _ = V.unleash_ext_with ty vargs in
    let vlam = Cx.eval cx tm in
    ret @@ Cx.quote cx ~ty @@ V.ext_apply vlam vargs
  | Tm.Cons (t0, _), Tm.Car ->
    ret t0
  | Tm.Cons (_, t1), Tm.Cdr ->
    ret t1
  | Tm.LblRet t, Tm.LblCall ->
    ret t
  | _ -> failwith "TODO: plug"

(* TODO: this sorry attempt results in things getting repeatedly evaluated *)
let (%%) (ty, tm) frame =
  base_cx >>= fun cx ->
  let vty = Cx.eval cx ty in
  plug (vty, tm) frame >>= fun tm' ->
  let vty' = Typing.infer cx @@ Tm.ann ~ty ~tm @< frame in
  let ty' = Cx.quote_ty cx vty' in
  ret (ty', tm')


let push_guess gm ~ty0 ~ty1 tm  =
  let alpha = Name.fresh () in
  let ty0' = abstract_ty gm ty0 in
  let ty1' = abstract_ty gm ty1 in
  let tm' = abstract_tm gm tm in
  let hd = Tm.Meta {name = alpha; ushift = 0} in
  let sp = telescope_to_spine gm in
  pushl @@ E (alpha, ty0', Guess {ty = ty1'; tm = tm'}) >>
  ret @@ Tm.up (hd, sp)



(* Check if the equation can *never* be satisfied.
   Remember that the equation is constrained to be well-typed in the appropriate
   heterogeneous sense, which means that if ty0,ty1 could never become equal, there
   is no need to compare tm0, tm1: such a case cannot arise based on how this
   function is called.

   LOL: I probably missed some cases. how horrific.
*)
let is_orthogonal q =
  match Tm.unleash q.tm0, Tm.unleash q.tm1 with
  | Tm.Up (Tm.Var _, _), Tm.Up (Tm.Var _, _) -> false
  | Tm.Up (Tm.Var _, _), Tm.Up (Tm.Meta _, _) -> false
  | Tm.Up (Tm.Var _, _), _ -> true

  | Tm.Up (Tm.Meta _, _), Tm.Up (Tm.Var _, _) -> false
  | Tm.Up (Tm.Meta _, _), Tm.Up (Tm.Meta _, _) -> false
  | _, Tm.Up (Tm.Var _, _) -> true

  | Tm.Pi _, Tm.Univ _ -> true
  | Tm.Pi _, Tm.Sg _ -> true
  | Tm.Pi _, Tm.Data _ -> true
  (* | Tm.Pi _, Tm.Rst _ -> true *)
  | Tm.Pi _, Tm.Ext _ -> true

  | Tm.Univ _, Tm.Pi _ -> true
  | Tm.Univ _, Tm.Sg _ -> true
  | Tm.Univ _, Tm.Data _ -> true
  (* | Tm.Univ _, Tm.Rst _ -> true *)
  | Tm.Univ _, Tm.Ext _ -> true

  | Tm.Sg _, Tm.Pi _ -> true
  | Tm.Sg _, Tm.Univ _ -> true
  | Tm.Sg _, Tm.Data _ -> true
  (* | Tm.Sg _, Tm.Rst _ -> true *)
  | Tm.Sg _, Tm.Ext _ -> true

  | Tm.Data _, Tm.Univ _ -> true
  | Tm.Data _, Tm.Sg _ -> true
  | Tm.Data _, Tm.Ext _ -> true
  | Tm.Data _, Tm.Pi _ -> true
  (* | Tm.Data _, Tm.Rst _ -> true *)

  (* | Tm.Rst _, Tm.Univ _ -> true
     | Tm.Rst _, Tm.Pi _ -> true
     | Tm.Rst _, Tm.Sg _ -> true
     | Tm.Rst _, Tm.Ext _ -> true
     | Tm.Rst _, Tm.Data _ -> true *)

  | Tm.Ext _, Tm.Pi _ -> true
  | Tm.Ext _, Tm.Sg _ -> true
  | Tm.Ext _, Tm.Univ _ -> true
  | Tm.Ext _, Tm.Data _ -> true
  (* | Tm.Ext _, Tm.Rst _ -> true *)

  | Tm.Data dlbl0, Tm.Data dlbl1 -> not (dlbl0 = dlbl1)
  | Tm.Intro (_, clbl0, _), Tm.Intro (_, clbl1, _) -> not (clbl0 = clbl1)

  | _ -> false

let rec match_spine x0 tw0 sp0 x1 tw1 sp1 =
  let rec go sp0 sp1 =
    match sp0, sp1 with
    | Emp, Emp ->
      if x0 = x1 then
        lookup_var x0 tw0 >>= fun ty0 ->
        lookup_var x1 tw1 >>= fun ty1 ->
        eval ty0 >>= fun vty0 ->
        eval ty1 >>= fun vty1 ->
        ret (vty0, vty1)
      else
        begin
          Format.eprintf "rigid head mismatch: %a <> %a@." Name.pp x0 Name.pp x1;
          failwith "rigid head mismatch"
        end

    | Snoc (sp0, Tm.FunApp t0), Snoc (sp1, Tm.FunApp t1) ->
      go sp0 sp1 >>= fun (ty0, ty1) ->
      evaluator >>= fun (cx, (module V)) ->
      let dom0, cod0 = V.unleash_pi ty0 in
      let dom1, cod1 = V.unleash_pi ty1 in
      let tdom0 = Cx.quote_ty cx dom0 in
      let tdom1 = Cx.quote_ty cx dom1 in
      active @@ Problem.eqn ~ty0:tdom0 ~ty1:tdom1 ~tm0:t0 ~tm1:t1 >>
      let cod0t0 = V.inst_clo cod0 @@ Cx.eval cx t0 in
      let cod0t1 = V.inst_clo cod1 @@ Cx.eval cx t1 in
      ret (cod0t0, cod0t1)

    | Snoc (sp0, Tm.ExtApp ts0), Snoc (sp1, Tm.ExtApp ts1) ->
      go sp0 sp1 >>= fun (ty0, ty1) ->
      evaluator >>= fun (cx, (module V)) ->
      let rs0 = List.map (Cx.eval_dim cx) ts0 in
      let rs1 = List.map (Cx.eval_dim cx) ts1 in
      (* TODO: unify the dimension spines ts0, ts1 *)
      let ty'0, sys0 = V.unleash_ext_with ty0 rs0 in
      let ty'1, sys1 = V.unleash_ext_with ty1 rs1 in
      (* let rst0 = D.make @@ D.Rst {ty = ty'0; sys = sys0} in
         let rst1 = D.make @@ D.Rst {ty = ty'1; sys = sys1} in *)
      ret (ty'0, ty'1)

    | Snoc (sp0, Tm.Car), Snoc (sp1, Tm.Car) ->
      go sp0 sp1 >>= fun (ty0, ty1) ->
      evaluator >>= fun (_, (module V)) ->
      let dom0, _ = V.unleash_sg ty0 in
      let dom1, _ = V.unleash_sg ty1 in
      ret (dom0, dom1)

    | Snoc (sp0, Tm.Cdr), Snoc (sp1, Tm.Cdr) ->
      go sp0 sp1 >>= fun (ty0, ty1) ->
      evaluator >>= fun (cx, (module V)) ->
      let _, cod0 = V.unleash_sg ty0 in
      let _, cod1 = V.unleash_sg ty1 in
      let cod0 = V.inst_clo cod0 @@ Cx.eval_cmd cx (Tm.Var {name = x0; twin = tw0; ushift = 0}, sp0 #< Tm.Car) in
      let cod1 = V.inst_clo cod1 @@ Cx.eval_cmd cx (Tm.Var {name = x1; twin = tw1; ushift = 0}, sp1 #< Tm.Car) in
      ret (cod0, cod1)

    | Snoc (sp0, Tm.LblCall), Snoc (sp1, Tm.LblCall) ->
      go sp0 sp1 >>= fun (ty0, ty1) ->
      evaluator >>= fun (_, (module V)) ->
      let _, _, ty0 = V.unleash_lbl_ty ty0 in
      let _, _, ty1 = V.unleash_lbl_ty ty1 in
      ret (ty0, ty1)


    (* TODO: Elim *)

    | Snoc (_sp0, Tm.VProj _info0), Snoc (_sp1, Tm.VProj _info1) ->
      failwith "TODO: match_spine/vproj"

    | Snoc (sp0, Tm.CoRForce), Snoc (sp1, Tm.CoRForce) ->
      go sp0 sp1

    | _ ->
      raise @@ E (SpineMismatch (sp0,sp1))

  in
  go sp0 sp1

let approx_sys ty0 sys0 ty1 sys1 =
  base_cx >>= fun cx ->
  let (module Q) = Cx.quoter cx in
  let vty0 = Cx.eval cx ty0 in
  let vty1 = Cx.eval cx ty1 in
  let vsys0 = Cx.eval_tm_sys cx sys0 in
  let vsys1 = Cx.eval_tm_sys cx sys1 in
  ret @@ Q.approx_restriction (Cx.qenv cx) vty0 vty1 vsys0 vsys1

let restriction_subtype ty0 sys0 ty1 sys1 =
  active @@ Subtype {ty0; ty1} >>
  approx_sys ty0 sys0 ty1 sys1



(* invariant: will not be called on inequations which are already reflexive *)
let rec subtype ty0 ty1 =
  if ty0 = ty1 then ret () else
    let univ = Tm.univ ~lvl:`Omega ~kind:`Pre in
    match Tm.unleash ty0, Tm.unleash ty1 with
    | Tm.Pi (dom0, cod0), Tm.Pi (dom1, cod1) ->
      let x = Name.fresh () in
      let cod0x = Tm.unbind_with (Tm.var x ~twin:`TwinL) cod0 in
      let cod1x = Tm.unbind_with (Tm.var x ~twin:`TwinR) cod1 in
      active @@ Subtype {ty0 = dom1; ty1 = dom0} >>
      active @@ Problem.all_twins x dom0 dom1 @@ Subtype {ty0 = cod0x; ty1 = cod1x}

    | Tm.Sg (dom0, cod0), Tm.Sg (dom1, cod1) ->
      let x = Name.fresh () in
      let cod0x = Tm.unbind_with (Tm.var x ~twin:`TwinL) cod0 in
      let cod1x = Tm.unbind_with (Tm.var x ~twin:`TwinR) cod1 in
      active @@ Subtype {ty0 = dom0; ty1 = dom1} >>
      active @@ Problem.all_twins x dom0 dom1 @@ Subtype {ty0 = cod0x; ty1 = cod1x}

    | Tm.Ext ebnd0, Tm.Ext ebnd1 ->
      let xs, ty0, sys0 = Tm.unbind_ext ebnd0 in
      let xs_fwd = Bwd.to_list xs in
      let ty1, sys1 = Tm.unbind_ext_with (List.map Tm.var xs_fwd) ebnd1 in
      let ps = List.map (fun x -> (x, `I)) xs_fwd in
      let rec go sys0 sys1 =
        match sys0, sys1 with
        | _, [] -> ret ()
        | (_, _, None) :: sys0, sys1 ->
          go sys0 sys1
        | sys0, (_, _, None) :: sys1 ->
          go sys0 sys1
        | (r0, r0', Some tm0) :: sys0, (r1, r1', Some tm1) :: sys1 when r0 = r1 && r0' = r1' ->
          under_restriction r0 r0' begin
            active @@ Problem.eqn ~ty0 ~ty1 ~tm0 ~tm1
          end >>
          go sys0 sys1
        | _ ->
          (* Format.eprintf "shoot??: %a <= %a@ / %a <= %a@." Tm.pp0 ty'0 Tm.pp0 ty'1 (Tm.pp_sys Pp.Env.emp) sys0 (Tm.pp_sys Pp.Env.emp) sys1; *)
          failwith "Extension subtype: nope"
      in
      in_scopes ps begin
        active @@ Subtype {ty0; ty1} >>
        go sys0 sys1
      end

    | Tm.Up (Tm.Meta _, _), Tm.Up (Tm.Meta _, _) ->
      (* no idea what to do in flex-flex case, don't worry about it *)
      active @@ Problem.eqn ~ty0:univ ~ty1:univ ~tm0:ty0 ~tm1:ty1

    (* The following two cases are sketchy: they do not yield most general solutions for subtyping.
       But it seems to be analogous to what happens in Agda. *)
    | Tm.Up (Tm.Meta _, _), _ ->
      active @@ Problem.eqn ~ty0:univ ~ty1:univ ~tm0:ty0 ~tm1:ty1

    | _, Tm.Up (Tm.Meta _, _) ->
      active @@ Problem.eqn ~ty0:univ ~ty1:univ ~tm0:ty0 ~tm1:ty1

    (* | Tm.Rst rst0, Tm.Rst rst1 ->
       restriction_subtype rst0.ty rst0.sys rst1.ty rst1.sys *)

    (* | Tm.Rst _, _ ->
       active @@ Subtype {ty0; ty1 = Tm.make @@ Tm.Rst {ty = ty1; sys = []}} *)

    | _ ->
      active @@ Problem.eqn ~ty0:univ ~ty1:univ ~tm0:ty0 ~tm1:ty1



let normalize_eqn q =
  base_cx >>= fun cx ->
  let vty0 = Cx.eval cx q.ty0 in
  let vty1 = Cx.eval cx q.ty1 in
  let el0 = Cx.eval cx q.tm0 in
  let el1 = Cx.eval cx q.tm1 in
  let tm0 = Cx.quote cx vty0 el0 in
  let tm1 = Cx.quote cx vty1 el1 in
  let ty0 = Cx.quote_ty cx vty0 in
  let ty1 = Cx.quote_ty cx vty1 in
  ret {ty0; ty1; tm0; tm1}

(* invariant: will not be called on equations which are already reflexive *)
let rigid_rigid q =
  normalize_eqn q >>= fun q ->
  match Tm.unleash q.tm0, Tm.unleash q.tm1 with
  | Tm.Pi (dom0, cod0), Tm.Pi (dom1, cod1) ->
    let x = Name.named @@ Some "rigidrigid-pi" in
    let cod0x = Tm.unbind_with (Tm.var x ~twin:`TwinL) cod0 in
    let cod1x = Tm.unbind_with (Tm.var x ~twin:`TwinR) cod1 in
    active @@ Problem.eqn ~ty0:q.ty0 ~tm0:dom0 ~ty1:q.ty1 ~tm1:dom1 >>
    active @@ Problem.all_twins x dom0 dom1 @@
    Problem.eqn ~ty0:q.ty0 ~tm0:cod0x ~ty1:q.ty1 ~tm1:cod1x

  | Tm.Sg (dom0, cod0), Tm.Sg (dom1, cod1) ->
    let x = Name.named @@ Some "rigidrigid-sg" in
    let cod0x = Tm.unbind_with (Tm.var x ~twin:`TwinL) cod0 in
    let cod1x = Tm.unbind_with (Tm.var x ~twin:`TwinR) cod1 in
    active @@ Problem.eqn ~ty0:q.ty0 ~tm0:dom0 ~ty1:q.ty1 ~tm1:dom1 >>
    active @@ Problem.all_twins x dom0 dom1 @@
    Problem.eqn ~ty0:q.ty0 ~tm0:cod0x ~ty1:q.ty1 ~tm1:cod1x

  | Tm.Up (Tm.Var info0, sp0), Tm.Up (Tm.Var info1, sp1) when info0.ushift = 0 && info1.ushift = 0 ->
    match_spine info0.name info0.twin sp0 info1.name info1.twin sp1 >>
    ret ()

  | _ ->
    if is_orthogonal q then
      begin
        Format.eprintf "rigid-rigid mismatch: %a@." Equation.pp q;
        failwith "rigid-rigid mismatch"
      end
    else
      block @@ Unify q

let unify q =
  match Tm.unleash q.ty0, Tm.unleash q.ty1 with
  | Tm.Pi (dom0, Tm.B (nm, _)), Tm.Pi (dom1, _) ->
    let x = Name.named nm in
    let x_l = Tm.up @@ Tm.var ~twin:`TwinL x in
    let x_r = Tm.up @@ Tm.var ~twin:`TwinR x in

    in_scope x (`Tw (dom0, dom1))
      begin
        (q.ty0, q.tm0) %% Tm.FunApp x_l >>= fun (ty0, tm0) ->
        (q.ty1, q.tm1) %% Tm.FunApp x_r >>= fun (ty1, tm1) ->
        ret @@ Problem.all_twins x dom0 dom1 @@ Problem.eqn ~ty0 ~tm0 ~ty1 ~tm1
      end >>= fun prob ->
    active prob

  | Tm.Sg (dom0, _), Tm.Sg (dom1, _) ->
    (* Format.eprintf "Unify: @[<1>%a@]@.@." Equation.pp q ; *)
    (q.ty0, q.tm0) %% Tm.Car >>= fun (_, car0) ->
    (q.ty1, q.tm1) %% Tm.Car >>= fun (_, car1) ->
    (q.ty0, q.tm0) %% Tm.Cdr >>= fun (ty_cdr0, cdr0) ->
    (q.ty1, q.tm1) %% Tm.Cdr >>= fun (ty_cdr1, cdr1) ->
    active @@ Problem.eqn ~ty0:dom0 ~tm0:car0 ~ty1:dom1 ~tm1:car1 >>
    let prob = Problem.eqn ~ty0:ty_cdr0 ~tm0:cdr0 ~ty1:ty_cdr1 ~tm1:cdr1 in
    (* Format.eprintf "problem: %a@.@." (Problem.pp) prob; *)
    active @@ prob

  | Tm.Ext (Tm.NB (nms0, (_ty0, _sys0))), Tm.Ext (Tm.NB (_nms1, (_ty1, _sys1))) ->
    let xs = Bwd.map Name.named nms0 in
    let xs_lst = Bwd.to_list xs in
    let vars = List.map (fun x -> Tm.up @@ Tm.var x) xs_lst in
    let psi =
      match xs_lst with
      | [] -> List.map (fun x -> (x, `I)) @@ xs_lst
      | _ -> [(Name.fresh (), `NullaryExt)]
    in

    in_scopes psi
      begin
        (q.ty0, q.tm0) %% Tm.ExtApp vars >>= fun (ty0, tm0) ->
        (q.ty1, q.tm1) %% Tm.ExtApp vars >>= fun (ty1, tm1) ->
        ret @@ Problem.all_dims xs_lst @@ Problem.eqn ~ty0 ~tm0 ~ty1 ~tm1
      end >>= fun prob ->
    active prob

  (* | Tm.Rst info0, Tm.Rst info1 ->
     active @@ Unify {q with ty0 = info0.ty; ty1 = info1.ty} *)

  | _ ->
    match Tm.unleash q.tm0, Tm.unleash q.tm1 with
    | Tm.Up (Tm.Meta {name = alpha0; ushift = ushift0}, sp0), Tm.Up (Tm.Meta {name = alpha1; ushift = ushift1}, sp1)
      when
        alpha0 = alpha1 && ushift0 = ushift1
      ->
      try_prune q <|| begin
        try_prune (Equation.sym q) <||
        flex_flex_same {q with tm0 = alpha0, sp0; tm1 = sp1}
      end

    | Tm.Up (Tm.Meta _, _), Tm.Up (Tm.Meta _, _) ->
      try_prune q <|| begin
        try_prune (Equation.sym q) <||
        flex_flex_diff [] q
      end

    | Tm.Up (Tm.Meta _, _), _ ->
      try_prune q <|| flex_term [] q

    | _, Tm.Up (Tm.Meta _, _) ->
      let q' = Equation.sym q in
      try_prune q' <|| flex_term [] q'

    | _ ->
      rigid_rigid q


let rec split_sigma tele x ty =
  match Tm.unleash ty with
  | Tm.Sg (dom, Tm.B (_, cod)) ->
    let y = Name.fresh () in
    let z = Name.fresh () in
    let sp_tele = telescope_to_spine tele in

    let ytm = Tm.Var {name = y; twin = `Only; ushift = 0}, sp_tele in
    let ztm = Tm.Var {name = z; twin = `Only; ushift = 0}, sp_tele in
    let cody = Tm.subst (Tm.dot ytm (Tm.shift 0)) cod in

    Some
      ( y
      , abstract_ty tele dom
      , z
      , abstract_ty tele cody
      , abstract_tm tele @@ Tm.cons (Tm.up ytm) (Tm.up ztm)
      , ( abstract_tm tele @@ Tm.up (Tm.Var {name = x; twin = `Only; ushift = 0}, sp_tele #< Tm.Car)
        , abstract_tm tele @@ Tm.up (Tm.Var {name = x; twin = `Only; ushift = 0}, sp_tele #< Tm.Cdr)
        )
      )


  | Tm.Pi (dom, cod) ->
    let y, cody = Tm.unbind cod in
    split_sigma (tele #< (y, `P dom)) x cody

  | _ ->
    None


let rec lower tele alpha ty =
  match Tm.unleash ty with
  | Tm.LblTy info ->
    hole `Flex tele info.ty @@ fun t ->
    define tele alpha `Transparent ~ty @@ Tm.make @@ Tm.LblRet (Tm.up t) >>
    ret true

  | Tm.Sg (dom, cod) ->
    hole `Flex tele dom @@ fun t0 ->
    in_scopes (Bwd.to_list tele) begin
      eval dom >>= fun vdom ->
      inst_ty_bnd cod (vdom, Tm.up t0)
    end >>= fun cod' ->
    hole `Flex tele cod' @@ fun t1 ->
    define tele alpha `Transparent ~ty @@ Tm.cons (Tm.up t0) (Tm.up t1) >>
    ret true


  | Tm.Pi (dom, (Tm.B (nm, _) as cod)) ->
    let x = Name.named nm in
    begin
      match split_sigma Emp x dom with
      | None ->
        let codx = Tm.unbind_with (Tm.var x) cod in
        lower (tele #< (x, `P dom)) alpha codx

      | Some (y, ty0, z, ty1, s, (u, v)) ->
        let tele' = tele #< (y, `P ty0) #< (z, `P ty1) in
        in_scopes (Bwd.to_list tele') begin
          eval @@ abstract_ty tele dom >>= fun vty ->
          begin
            inst_ty_bnd cod (vty, s) >>= fun cod' ->
            ret @@ abstract_ty (Emp #< (y, `P ty0) #< (z, `P ty1)) cod'
          end
        end >>= fun pi_ty ->
        hole `Flex tele pi_ty @@ fun (whd, wsp) ->
        let bdy = Tm.up (whd, wsp #< (Tm.FunApp u) #< (Tm.FunApp v)) in
        define tele alpha `Transparent ~ty @@ Tm.make @@ Tm.Lam (Tm.bind x bdy) >>
        ret true
    end

  | _ ->
    ret false

let is_reflexive q =
  let univ = Tm.univ ~lvl:`Omega ~kind:`Pre in
  check_eq ~ty:univ q.ty0 q.ty1 >>= function
  | `Ok ->
    begin
      check_eq ~ty:q.ty0 q.tm0 q.tm1 >>= function
      | `Ok -> ret true
      | _ -> ret false
    end
  | `Exn _ ->
    ret false


let is_restriction =
  function
  | `R _ -> true
  | _ -> false

let rec solver prob =
  match prob with
  | Unify q ->
    is_reflexive q <||
    unify q

  | Subtype {ty0; ty1} ->
    begin
      check_subtype ty0 ty1 >>= function
      | `Ok ->
        ret ()
      | _ ->
        subtype ty0 ty1
    end

  | All (param, prob) ->
    let x, probx = unbind param prob in
    if not (is_restriction param || Occurs.Set.mem x @@ Problem.free `Vars probx) then
      active probx
    else
      begin
        match param with
        | `I | `Tick | `NullaryExt | `KillFromTick _ | `SelfArg _ as p ->
          in_scope x p @@
          solver probx

        | `P ty ->
          begin
            match split_sigma Emp x ty with
            | Some (y, ty0, z, ty1, s, _) ->
              (in_scopes [(y, `P ty0); (z, `P ty1)] get_global_env) >>= fun env ->
              solver @@ Problem.all y ty0 @@ Problem.all z ty1 @@
              Problem.subst (GlobalEnv.define env x ~ty ~tm:s) probx
            | None ->
              in_scope x (`P ty) @@
              solver probx
          end

        | `Def (ty, tm) ->
          begin
            (* match split_sigma Emp x ty with
               | Some (y, ty0, z, ty1, s, _) ->
               (in_scopes [(y, `P ty0); (z, `P ty1)] get_global_env) >>= fun env ->
               solver @@ Problem.all y ty0 @@ Problem.all z ty1 @@
               Problem.subst (GlobalEnv.define env x ~ty ~tm:s) probx
               | None -> *)
            in_scope x (`Def (ty, tm)) @@
            solver probx
          end

        | `Tw (ty0, ty1) ->
          let univ = Tm.univ ~lvl:`Omega ~kind:`Pre in
          begin
            check_eq ~ty:univ ty0 ty1 >>= function
            | `Ok ->
              get_global_env >>= fun sub ->
              let y = Name.named (Name.name x) in
              (*  This weird crap is needed to avoid creating a cycle in the environment.
                  What we should really do is kill 'twin variables' altogether and switch to
                  a representation based on having two contexts. *)
              let var_y = Tm.up @@ Tm.var y in
              let var_x = Tm.up @@ Tm.var x in
              let sub_y = Subst.define (Subst.ext sub y (`P {ty = ty0; sys = []})) x ~ty:ty0 ~tm:var_y in
              let sub_x = Subst.define (Subst.ext sub x (`P {ty = ty0; sys = []})) y ~ty:ty0 ~tm:var_x in
              solver @@ Problem.all x ty0 @@
              Problem.subst sub_x @@ Problem.subst sub_y probx
            | _ ->
              in_scope x (`Tw (ty0, ty1)) @@
              solver probx
          end

        | `R (r0, r1) ->
          check_eq_dim r0 r1 >>= function
          | true ->
            solver probx
          | false ->
            under_restriction r0 r1 @@ solver probx >>
            ret ()
      end


(* guess who named this function, lol *)
let ambulando =
  fix @@ fun loop ->
  popr_opt >>= function
  | None ->
    ret ()

  | Some e ->
    match e with
    | E (alpha, ty, Hole `Flex) ->
      begin
        lower Emp alpha ty <||
        pushl e
      end >>
      loop

    | E (_, _, Hole `Rigid) ->
      pushl e >>
      loop

    | E (alpha, ty, Guess info) ->
      begin
        check ~ty info.tm >>= function
        | `Ok ->
          (* Format.eprintf "solved guess %a??@." Name.pp alpha; *)
          pushl @@ E (alpha, ty, Defn (`Transparent, info.tm)) >>
          push_update alpha >>
          loop
        | _ ->
          (* dump_state Format.err_formatter "failed to solve guess" `All >>= fun _ -> *)
          (* Format.eprintf "Failed to solve guess %a@." Name.pp alpha; *)
          pushl e >>
          loop
      end

    | Q (Active, prob) ->
      solver prob >>
      loop

    | _ ->
      pushl e >>
      loop
