open RedBasis
open Bwd open BwdNotation
open Contextual
open Dev

module Notation = Monad.Notation (Contextual)
open Notation

type telescope = (Name.t * ty) bwd

let rec telescope ty =
  match Tm.unleash ty with
  | Tm.Pi (dom, cod) ->
    let x, codx = Tm.unbind cod in
    let (tel, ty) = telescope codx in
    (Emp #< (x, dom)) <.> tel, ty
  | _ ->
    Emp, ty

let rec lambdas xs tm =
  match xs with
  | Emp -> tm
  | Snoc (xs, x) ->
    lambdas xs @@ Tm.make @@ Tm.Lam (Tm.bind x tm)

let rec pis gm tm =
  match gm with
  | Emp -> tm
  | Snoc (gm, (x, ty)) ->
    pis gm @@ Tm.make @@ Tm.Pi (ty, Tm.bind x tm)

let telescope_to_spine =
  (* TODO: might be backwards *)
  Bwd.map @@ fun (x, _) ->
  Tm.FunApp (Tm.up (Tm.Ref (x, `Only), Emp))

let hole_named alpha gm ty f =
  pushl (E (alpha, pis gm ty, Hole)) >>
  let hd = Tm.Meta alpha in
  let sp = telescope_to_spine gm in
  f (hd, sp) >>= fun r ->
  go_left >>
  ret r

let hole gm ty f =
  hole_named (Name.fresh ()) gm ty f

let define gm alpha ~ty tm =
  let ty' = pis gm ty in
  let tm' = lambdas (Bwd.map fst gm) tm in
  pushr @@ E (alpha, ty', Defn tm')

(* This is a crappy version of occurs check, not distingiushing between strong rigid and weak rigid contexts.
   Later on, we can improve it. *)
let occurs_check alpha tm =
  Occurs.Set.mem alpha @@
  Tm.free `Metas tm



(* A very crappy eta contraction function. It's horrific that this is actually a thing that we do! *)
let rec eta_contract t =
  match Tm.unleash t with
  | Tm.Lam bnd ->
    let y, tmy = Tm.unbind bnd in
    let tm'y = eta_contract tmy in
    begin
      match Tm.unleash tm'y with
      | Tm.Up (Tm.Ref (f, twf), Snoc (sp, Tm.FunApp arg)) ->
        begin
          match Tm.unleash arg with
          | Tm.Up (Tm.Ref (y', _), Emp)
            when
              y = y'
              && not @@ Occurs.Set.mem y @@ Tm.Sp.free `Vars sp
            ->
            Tm.up (Tm.Ref (f, twf), sp)
          | _ ->
            Tm.make @@ Tm.Lam (Tm.bind y tm'y)
        end
      | _ ->
        Tm.make @@ Tm.Lam (Tm.bind y tm'y)
    end

  | Tm.Cons (t0, t1) ->
    let t0' = eta_contract t0 in
    let t1' = eta_contract t1 in
    begin
      match Tm.unleash t0', Tm.unleash t1' with
      | Tm.Up (hd0, Snoc (sp0, Tm.Car)), Tm.Up (hd1, Snoc (sp1, Tm.Cdr))
        when
          hd0 = hd1 && sp0 = sp1
        ->
        Tm.up (hd0, sp0)
      | _ ->
        Tm.cons t0' t1'
    end

  | con ->
    Tm.make @@ Tm.map_tmf eta_contract con

let to_var t =
  match Tm.unleash @@ eta_contract t with
  | Tm.Up (Tm.Ref (a, _), Emp) ->
    Some a
  | _ ->
    None

let rec spine_to_vars sp =
  match sp with
  | Emp -> Some Emp
  | Snoc (sp, Tm.FunApp t) ->
    begin
      match to_var t with
      | Some x -> Option.map (fun xs -> xs #< x) @@ spine_to_vars sp
      | None -> None
    end
  | _ -> None

let linear_on t =
  let fvs = Tm.free `Vars t in
  let rec go xs =
    match xs with
    | Emp -> true
    | Snoc (xs, x) ->
      not (Occurs.Set.mem x fvs && List.mem x @@ Bwd.to_list xs) && go xs
  in go

let invert alpha ty sp t =
  if occurs_check alpha t then
    failwith "occurs check"
  else (* alpha does not occur in t *)
    match spine_to_vars sp with
    | Some xs when linear_on t xs ->
      let lam_tm = lambdas xs t in
      local (fun _ -> Emp) begin
        check ~ty lam_tm >>
        ret true
      end >>= fun b ->
      ret @@ if b then Some lam_tm else None
    | _ ->
      ret None

let try_invert q ty =
  match Tm.unleash q.tm0 with
  | Tm.Up (Meta alpha, sp) ->
    begin
      invert alpha ty sp q.tm1 >>= function
      | None ->
        ret false
      | Some t ->
        active (Unify q) >>
        define Emp alpha ~ty t >>
        ret true
    end
  | _ ->
    failwith "try_invert"

let rec flex_term ~deps q =
  match Tm.unleash q.tm0 with
  | Tm.Up (Meta alpha, _) ->
    Bwd.map snd <@> ask >>= fun gm ->
    popl >>= fun e ->
    begin
      match e with
      | E (beta, _, Hole) when alpha = beta && Occurs.Set.mem alpha @@ Entries.free `Metas deps ->
        pushls (e :: deps) >>
        block (Unify q)
      | E (beta, ty, Hole) when alpha = beta ->
        pushls deps >>
        try_invert q ty <||
        begin
          block (Unify q) >>
          pushl e
        end
      | E (beta, _, Hole)
        when
          Occurs.Set.mem beta (Params.free `Metas gm)
          || Occurs.Set.mem beta (Entries.free `Metas deps)
          || Occurs.Set.mem beta (Equation.free `Metas q)
        ->
        flex_term ~deps:(e :: deps) q
      | _ ->
        pushr e >>
        flex_term ~deps q
    end
  | _ -> failwith "flex_term"


let rec flex_flex_diff ~deps q =
  match Tm.unleash q.tm0, Tm.unleash q.tm1 with
  | Tm.Up (Tm.Meta alpha0, _), Tm.Up (Tm.Meta alpha1, _) ->
    Bwd.map snd <@> ask >>= fun gm ->
    begin
      popl >>= function
      | E (gamma, _, Hole) as e
        when
          (alpha0 = gamma || alpha1 = gamma)
          && Occurs.Set.mem gamma @@ Entries.free `Metas deps
        ->
        pushls (e :: deps) >>
        block (Unify q)

      | E (gamma, ty, Hole) as e when gamma = alpha0 ->
        pushls deps >>
        try_invert q ty <||
        flex_term [e] (Equation.sym q)

      | E (gamma, _, Hole) as e
        when
          Occurs.Set.mem gamma @@ Params.free `Metas gm
          || Occurs.Set.mem gamma @@ Entries.free `Metas deps
          || Occurs.Set.mem gamma @@ Equation.free `Metas q
        ->
        flex_flex_diff ~deps:(e :: deps) q

      | e ->
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
  | E (beta, ty', Hole) when alpha = beta ->
    hole Emp ty @@ fun cmd ->
    define Emp beta ~ty:ty' @@ f cmd
  | e ->
    pushr e >>
    instantiate inst

let flex_flex_same q =
  let alpha, sp0 = q.tm0 in
  let sp1 = q.tm1 in
  lookup_meta alpha >>= fun ty_alpha ->
  let tele, cod = telescope ty_alpha in
  match intersect tele sp0 sp1 with
  | Some tele' ->
    let f (hd, sp) =
      lambdas (Bwd.map fst tele) @@
      let sp' = telescope_to_spine tele in
      Tm.up (hd, sp <.> sp')
    in
    instantiate (alpha, pis tele' cod, f)
  | None ->
    block @@ Unify
      {q with
       tm0 = Tm.up (Tm.Meta alpha, sp0);
       tm1 = Tm.up (Tm.Meta alpha, sp1)}

let try_prune _q =
  (* TODO: implement pruning *)
  ret false

let normalize (module T : Typing.S) ~ty tm =
  let lcx = T.Cx.emp in
  let vty = T.Cx.eval lcx ty in
  let el = T.Cx.eval lcx tm in
  ret @@ T.Cx.quote lcx ~ty:vty el


(* This is all so horrible because we don't have hereditary-substitution-style operations
   directly on the syntax. So we have to factor through evaluation and quotation all the time.

   While checking conversion is most convenient with NBE, it seems that elaboration and
   unification would be better served by a purely syntactic approach based on hereditary
   substitution. *)


module HSubst (T : Typing.S) =
struct
  let inst_ty_bnd bnd (arg_ty, arg) =
    let Tm.B (nm, tm) = bnd in
    let varg = T.Cx.eval T.Cx.emp arg in
    let lcx = T.Cx.def T.Cx.emp ~nm ~ty:arg_ty ~el:varg in
    let el = T.Cx.eval lcx tm in
    T.Cx.quote_ty T.Cx.emp el

  let inst_bnd (ty_clo, tm_bnd) (arg_ty, arg) =
    let Tm.B (nm, tm) = tm_bnd in
    let varg = T.Cx.eval T.Cx.emp arg in
    let lcx = T.Cx.def T.Cx.emp ~nm ~ty:arg_ty ~el:varg in
    let el = T.Cx.eval lcx tm in
    let vty = T.Cx.Eval.inst_clo ty_clo varg in
    T.Cx.quote T.Cx.emp ~ty:vty el

  let plug (ty, tm) frame =
    match Tm.unleash tm, frame with
    | Tm.Up (hd, sp), _ ->
      Tm.up (hd, sp #< frame)
    | Tm.Lam bnd, Tm.FunApp arg ->
      let dom, cod = T.Cx.Eval.unleash_pi ty in
      inst_bnd (cod, bnd) (dom, arg)
    | _, Tm.ExtApp _ ->
      failwith "TODO: %%/ExtApp"
    | Tm.Cons (t0, _), Tm.Car -> t0
    | Tm.Cons (_, t1), Tm.Cdr -> t1
    | Tm.LblRet t, Tm.LblCall -> t
    | Tm.Tt, Tm.If info -> info.tcase
    | Tm.Ff, Tm.If info -> info.fcase
    | _ -> failwith "TODO: %%"

  (* TODO: this sorry attempt results in things getting repeatedly evaluated *)
  let (%%) (ty, tm) frame =
    let vty = T.Cx.eval T.Cx.emp ty in
    let tm' = plug (vty, tm) frame in
    let el = T.Cx.eval T.Cx.emp tm' in
    let vty' = T.infer_frame T.Cx.emp ~ty:vty ~hd:el frame in
    let ty' = T.Cx.quote_ty T.Cx.emp vty' in
    ty', tm'
end


(* Check if the equation can *never* be satisfied.
   Remember that the equation is constrained to be well-typed in the appropriate
   heterogeneous sense, which means that if ty0,ty1 could never become equal, there
   is no need to compare tm0, tm1: such a case cannot arise based on how this
   function is called.

   LOL: I probably missed some cases. how horrific.
*)
let is_orthogonal q =
  match Tm.unleash q.tm0, Tm.unleash q.tm1 with
  | Tm.Up (Tm.Ref _, _), Tm.Up (Tm.Ref _, _) -> false
  | Tm.Up (Tm.Ref _, _), Tm.Up (Tm.Meta _, _) -> false
  | Tm.Up (Tm.Ref _, _), _ -> true

  | Tm.Up (Tm.Meta _, _), Tm.Up (Tm.Ref _, _) -> false
  | Tm.Up (Tm.Meta _, _), Tm.Up (Tm.Meta _, _) -> false
  | _, Tm.Up (Tm.Ref _, _) -> true

  | Tm.Pi _, Tm.Univ _ -> true
  | Tm.Pi _, Tm.Sg _ -> true
  | Tm.Pi _, Tm.Bool -> true
  | Tm.Pi _, Tm.Rst _ -> true
  | Tm.Pi _, Tm.Ext _ -> true

  | Tm.Univ _, Tm.Pi _ -> true
  | Tm.Univ _, Tm.Sg _ -> true
  | Tm.Univ _, Tm.Bool -> true
  | Tm.Univ _, Tm.Rst _ -> true
  | Tm.Univ _, Tm.Ext _ -> true

  | Tm.Sg _, Tm.Pi _ -> true
  | Tm.Sg _, Tm.Univ _ -> true
  | Tm.Sg _, Tm.Bool -> true
  | Tm.Sg _, Tm.Rst _ -> true
  | Tm.Sg _, Tm.Ext _ -> true

  | Tm.Bool, Tm.Univ _ -> true
  | Tm.Bool, Tm.Sg _ -> true
  | Tm.Bool, Tm.Ext _ -> true
  | Tm.Bool, Tm.Pi _ -> true
  | Tm.Bool, Tm.Rst _ -> true

  | Tm.Rst _, Tm.Univ _ -> true
  | Tm.Rst _, Tm.Pi _ -> true
  | Tm.Rst _, Tm.Sg _ -> true
  | Tm.Rst _, Tm.Ext _ -> true
  | Tm.Rst _, Tm.Bool -> true

  | Tm.Ext _, Tm.Pi _ -> true
  | Tm.Ext _, Tm.Sg _ -> true
  | Tm.Ext _, Tm.Univ _ -> true
  | Tm.Ext _, Tm.Bool -> true
  | Tm.Ext _, Tm.Rst _ -> true

  | Tm.Tt, Tm.Ff -> true
  | Tm.Ff, Tm.Tt -> true

  | _ -> false

let rec match_spine x0 tw0 sp0 x1 tw1 sp1 =
  typechecker >>= fun (module T) ->
  let module HSubst = HSubst (T) in
  let rec go sp0 sp1 =
    match sp0, sp1 with
    | Emp, Emp ->
      if x0 = x1 then
        lookup_var x0 tw0 >>= fun ty0 ->
        lookup_var x1 tw1 >>= fun ty1 ->
        let vty0 = T.Cx.eval T.Cx.emp ty0 in
        let vty1 = T.Cx.eval T.Cx.emp ty1 in
        ret (vty0, vty1)
      else
        failwith "rigid head mismatch"

    | Snoc (sp0, Tm.FunApp t0), Snoc (sp1, Tm.FunApp t1) ->
      go sp0 sp1 >>= fun (ty0, ty1) ->
      let dom0, cod0 = T.Cx.Eval.unleash_pi ty0 in
      let dom1, cod1 = T.Cx.Eval.unleash_pi ty1 in
      let tdom0 = T.Cx.quote_ty T.Cx.emp dom0 in
      let tdom1 = T.Cx.quote_ty T.Cx.emp dom1 in
      active @@ Problem.eqn ~ty0:tdom0 ~ty1:tdom1 ~tm0:t0 ~tm1:t1 >>
      let cod0t0 = T.Cx.Eval.inst_clo cod0 @@ T.Cx.eval T.Cx.emp t0 in
      let cod0t1 = T.Cx.Eval.inst_clo cod1 @@ T.Cx.eval T.Cx.emp t1 in
      ret (cod0t0, cod0t1)

    | Snoc (sp0, Tm.ExtApp ts0), Snoc (sp1, Tm.ExtApp ts1) ->
      go sp0 sp1 >>= fun (ty0, ty1) ->
      let rs0 = List.map (fun t -> T.Cx.unleash_dim T.Cx.emp @@ T.Cx.eval_dim T.Cx.emp t) ts0 in
      let rs1 = List.map (fun t -> T.Cx.unleash_dim T.Cx.emp @@ T.Cx.eval_dim T.Cx.emp t) ts1 in
      (* TODO: unify the dimension spines ts0, ts1 *)
      let ty'0, sys0 = T.Cx.Eval.unleash_ext ty0 rs0 in
      let ty'1, sys1 = T.Cx.Eval.unleash_ext ty1 rs1 in
      let rst0 = T.Cx.Eval.make @@ Val.Rst {ty = ty'0; sys = sys0} in
      let rst1 = T.Cx.Eval.make @@ Val.Rst {ty = ty'1; sys = sys1} in
      ret (rst0, rst1)

    | Snoc (sp0, Tm.Car), Snoc (sp1, Tm.Car) ->
      go sp0 sp1 >>= fun (ty0, ty1) ->
      let dom0, _ = T.Cx.Eval.unleash_sg ty0 in
      let dom1, _ = T.Cx.Eval.unleash_sg ty1 in
      ret (dom0, dom1)

    | Snoc (sp0, Tm.Cdr), Snoc (sp1, Tm.Cdr) ->
      go sp0 sp1 >>= fun (ty0, ty1) ->
      let _, cod0 = T.Cx.Eval.unleash_sg ty0 in
      let _, cod1 = T.Cx.Eval.unleash_sg ty1 in
      let cod0 = T.Cx.Eval.inst_clo cod0 @@ T.Cx.eval_cmd T.Cx.emp (Tm.Ref (x0, tw0), sp0 #< Tm.Car) in
      let cod1 = T.Cx.Eval.inst_clo cod1 @@ T.Cx.eval_cmd T.Cx.emp (Tm.Ref (x1, tw1), sp1 #< Tm.Car) in
      ret (cod0, cod1)

    | Snoc (sp0, Tm.LblCall), Snoc (sp1, Tm.LblCall) ->
      go sp0 sp1 >>= fun (ty0, ty1) ->
      let _, _, ty0 = T.Cx.Eval.unleash_lbl_ty ty0 in
      let _, _, ty1 = T.Cx.Eval.unleash_lbl_ty ty1 in
      ret (ty0, ty1)

    | Snoc (sp0, Tm.If info0), Snoc (sp1, Tm.If info1) ->
      go sp0 sp1 >>= fun (_ty0, _ty1) ->
      let y = Name.fresh () in
      let mot0y = Tm.unbind_with y `TwinL info0.mot in
      let mot1y = Tm.unbind_with y `TwinR info1.mot in
      let univ = Tm.univ ~lvl:Lvl.Omega ~kind:Kind.Pre in
      active @@ Problem.all y (Tm.make Tm.Bool) @@
      Problem.eqn ~ty0:univ ~ty1:univ ~tm0:mot0y ~tm1:mot1y
      >>
      let bool = T.Cx.Eval.make Val.Bool in
      let mot0_tt = HSubst.inst_ty_bnd info0.mot (bool, Tm.make Tm.Tt) in
      let mot0_ff = HSubst.inst_ty_bnd info0.mot (bool, Tm.make Tm.Ff) in
      let mot1_tt = HSubst.inst_ty_bnd info1.mot (bool, Tm.make Tm.Tt) in
      let mot1_ff = HSubst.inst_ty_bnd info1.mot (bool, Tm.make Tm.Ff) in
      active @@ Problem.eqn ~ty0:mot0_tt ~tm0:info0.tcase ~ty1:mot1_tt ~tm1:info1.tcase >>
      active @@ Problem.eqn ~ty0:mot0_ff ~tm0:info0.fcase ~ty1:mot1_ff ~tm1:info1.fcase >>
      let ty0 = T.Cx.eval T.Cx.emp @@ HSubst.inst_ty_bnd info0.mot (bool, Tm.up (Tm.Ref (x0, tw0), sp0)) in
      let ty1 = T.Cx.eval T.Cx.emp @@ HSubst.inst_ty_bnd info1.mot (bool, Tm.up (Tm.Ref (x1, tw1), sp1)) in
      ret (ty0, ty1)

    | Snoc (_sp0, Tm.VProj _info0), Snoc (_sp1, Tm.VProj _info1) ->
      failwith "TODO: match_spine/vproj"

    | _ -> failwith "spine mismatch"

  in
  go sp0 sp1

(* invariant: will not be called on equations which are already reflexive *)
let rigid_rigid q =
  match Tm.unleash q.tm0, Tm.unleash q.tm1 with
  | Tm.Pi (dom0, cod0), Tm.Pi (dom1, cod1) ->
    let x = Name.fresh () in
    let cod0x = Tm.unbind_with x `TwinL cod0 in
    let cod1x = Tm.unbind_with x `TwinR cod1 in
    active @@ Problem.eqn ~ty0:q.ty0 ~tm0:dom0 ~ty1:q.ty1 ~tm1:dom1 >>
    active @@ Problem.all_twins x dom0 dom1 @@
    Problem.eqn ~ty0:q.ty0 ~tm0:cod0x ~ty1:q.ty1 ~tm1:cod1x

  | Tm.Sg (dom0, cod0), Tm.Sg (dom1, cod1) ->
    let x = Name.fresh () in
    let cod0x = Tm.unbind_with x `TwinL cod0 in
    let cod1x = Tm.unbind_with x `TwinR cod1 in
    active @@ Problem.eqn ~ty0:q.ty0 ~tm0:dom0 ~ty1:q.ty1 ~tm1:dom1 >>
    active @@ Problem.all_twins x dom0 dom1 @@
    Problem.eqn ~ty0:q.ty0 ~tm0:cod0x ~ty1:q.ty1 ~tm1:cod1x

  | Tm.Up (Tm.Ref (x0, tw0), sp0), Tm.Up (Tm.Ref (x1, tw1), sp1) ->
    match_spine x0 tw0 sp0 x1 tw1 sp1 >>
    ret ()

  | _ ->
    if is_orthogonal q then
      failwith "rigid-rigid mismatch"
    else
      block @@ Unify q


let unify q =
  typechecker >>= fun (module T) ->
  let module HS = HSubst (T) in
  let open HS in

  match Tm.unleash q.ty0, Tm.unleash q.ty1 with
  | Tm.Pi (dom0, _), Tm.Pi (dom1, _) ->
    let x = Name.fresh () in
    let x_l = Tm.up (Tm.Ref (x, `TwinL), Emp) in
    let x_r = Tm.up (Tm.Ref (x, `TwinR), Emp) in
    let ty0, tm0 = (q.ty0, q.tm0) %% Tm.FunApp x_l in
    let ty1, tm1 = (q.ty1, q.tm1) %% Tm.FunApp x_r in
    active @@ Problem.all_twins x dom0 dom1 @@ Problem.eqn ~ty0 ~tm0 ~ty1 ~tm1

  | Tm.Sg (dom0, _), Tm.Sg (dom1, _) ->
    let _, car0 = (q.ty0, q.tm0) %% Tm.Car in
    let _, car1 = (q.ty1, q.tm1) %% Tm.Car in
    let ty_cdr0, cdr0 = (q.ty0, q.tm0) %% Tm.Cdr in
    let ty_cdr1, cdr1 = (q.ty1, q.tm1) %% Tm.Cdr in
    active @@ Problem.eqn ~ty0:dom0 ~tm0:car0 ~ty1:dom1 ~tm1:car1 >>
    active @@ Problem.eqn ~ty0:ty_cdr0 ~tm0:cdr0 ~ty1:ty_cdr1 ~tm1:cdr1

  | _ ->
    match Tm.unleash q.tm0, Tm.unleash q.tm1 with
    | Tm.Up (Tm.Meta alpha0, sp0), Tm.Up (Tm.Meta alpha1, sp1)
      when
        alpha0 = alpha1
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


let is_reflexive q =
  let univ = Tm.univ ~lvl:Lvl.Omega ~kind:Kind.Pre in
  check_eq ~ty:univ q.ty0 q.ty1 >>= function
  | true ->
    check_eq ~ty:q.ty0 q.tm0 q.tm1
  | false ->
    ret false

let rec solver =
  function
  | Unify q ->
    is_reflexive q <||
    unify q

  | All (param, prob) ->
    let x, probx = unbind prob in
    if not @@ Occurs.Set.mem x @@ Problem.free `Vars probx then
      active probx
    else
      match param with
      | P ty ->
        (* TODO: split sigma, blah blah *)
        in_scope x (P ty) @@
        solver probx

      | Tw (ty0, ty1) ->
        let univ = Tm.univ ~lvl:Lvl.Omega ~kind:Kind.Pre in
        check_eq ~ty:univ ty0 ty1 >>= function
        | true ->
          let var = Tm.up (Tm.Ref (x, `Only), Emp) in
          let sigma = Subst.define Subst.emp x ~ty:ty0 ~tm:var in
          solver @@ Problem.all x ty0 @@
          Problem.subst sigma probx
        | false ->
          in_scope x (Tw (ty0, ty1)) @@
          solver probx


let lower tele alpha ty =
  match Tm.unleash ty with
  | Tm.LblTy info ->
    hole tele info.ty @@ fun t ->
    define tele alpha ~ty @@ Tm.make @@ Tm.LblRet (Tm.up t) >>
    ret true

  | Tm.Sg (dom, Tm.B (_, cod)) ->
    hole tele dom @@ fun t0 ->
    hole tele (Tm.subst (Tm.Sub (Tm.Id, t0)) cod) @@ fun t1 ->
    define tele alpha ~ty @@ Tm.cons (Tm.up t0) (Tm.up t1) >>
    ret true

  | _ ->
    (* TODO: implement lowering *)
    ret false

(* guess who named this function, lol *)
let rec ambulando bracket =
  popr_opt >>= function
  | None ->
    ret ()

  | Some e ->
    match e with
    | E (alpha, ty, Hole) ->
      begin
        lower Emp alpha ty <||
        pushl e
      end >>
      ambulando bracket

    | Q (Active, prob) ->
      solver prob >>
      ambulando bracket

    | Bracket bracket' when bracket = bracket' ->
      ret ()

    | _ ->
      pushl e >>
      ambulando bracket
