open RedBasis
open Bwd open BwdNotation
open Contextual
open Dev

module Notation = Monad.Notation (Contextual)
open Notation

type telescope = params



let rec telescope ty : telescope * ty =
  match Tm.unleash ty with
  | Tm.Pi (dom, cod) ->
    let x, codx = Tm.unbind cod in
    let (tel, ty) = telescope codx in
    (Emp #< (x, `P dom)) <.> tel, ty
  | Tm.CoR (r, r', Some ty) ->
    let x = Name.fresh () in
    let (tel, ty) = telescope ty in
    (Emp #< (x, `R (r, r'))) <.> tel, ty
  | _ ->
    Emp, ty

let rec abstract_tm xs tm =
  match xs with
  | Emp -> tm
  | Snoc (xs, (x, `P _)) ->
    abstract_tm xs @@ Tm.make @@ Tm.Lam (Tm.bind x tm)
  | Snoc (xs, (x, `I)) ->
    let bnd = Tm.NB ([None], Tm.close_var x (fun _ -> `Only) 0 tm) in
    abstract_tm xs @@ Tm.make @@ Tm.ExtLam bnd
  | Snoc (xs, (_, `R (r, r'))) ->
    abstract_tm xs @@ Tm.make @@ Tm.CoRThunk (r, r', Some tm)
  | _ ->
    failwith "abstract_tm"

let rec abstract_ty (gm : telescope) cod =
  match gm with
  | Emp -> cod
  | Snoc (gm, (x, `P dom)) ->
    abstract_ty gm @@ Tm.make @@ Tm.Pi (dom, Tm.bind x cod)
  | Snoc (gm, (_, `R (r, r'))) ->
    abstract_ty gm @@ Tm.make @@ Tm.CoR (r, r', Some cod)
  | Snoc (gm, (x, `I)) ->
    let cod' = Tm.close_var x (fun tw -> tw) 0 cod in
    abstract_ty gm @@ Tm.make @@ Tm.Ext (Tm.NB ([Name.name x], (cod', [])))
  | _ ->
    failwith "abstract_ty"

let telescope_to_spine : telescope -> tm Tm.spine =
  (* TODO: might be backwards *)
  Bwd.map @@ fun (x, param) ->
  match param with
  | `I ->
    Tm.ExtApp [Tm.up (Tm.Ref (x, `Only), Emp)]
  | `P _ ->
    Tm.FunApp (Tm.up (Tm.Ref (x, `Only), Emp))
  | `R _ ->
    Tm.CoRForce
  | _ ->
    failwith "TODO: telescope_to_spine"

let push_hole tag gm ty =
  let alpha = Name.fresh () in
  pushl (E (alpha, abstract_ty gm ty, Hole tag)) >>
  let hd = Tm.Meta alpha in
  let sp = telescope_to_spine gm in
  ret (hd, sp)

let hole tag gm ty f =
  push_hole tag gm ty >>= fun cmd ->
  f cmd >>= fun r ->
  go_left >>
  ret r

let define gm alpha ~ty tm =
  let ty' = abstract_ty gm ty in
  let tm' = abstract_tm gm tm in
  check ~ty:ty' tm' >>= fun b ->
  if not b then
    dump_state Format.err_formatter "Type error" `All >>= fun _ ->
    begin
      Format.eprintf "error checking: %a : %a@." Tm.pp0 tm' Tm.pp0 ty';
      failwith "define: type error"
    end
  else
    push_update alpha >>
    pushr @@ E (alpha, ty', Defn tm')

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
  | Tm.Up (Tm.Ref (a, _), Emp) ->
    Some a
  | _ ->
    (* Format.eprintf "to_var: %a@.@." (Tm.pp Pretty.Env.emp) t; *)
    None


let rec spine_to_tele sp =
  match sp with
  | Emp -> Some Emp
  | Snoc (sp, Tm.FunApp t) ->
    begin
      match to_var t with
      | Some x -> Option.map (fun xs -> xs #< (x, `P ())) @@ spine_to_tele sp
      | None -> None
    end
  | Snoc (sp, Tm.ExtApp ts) ->
    begin
      match opt_traverse to_var ts with
      | Some xs -> Option.map (fun ys -> ys <>< List.map (fun x -> (x, `I)) xs) @@ spine_to_tele sp
      | None -> None
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
    | Snoc (_, _) ->
      failwith "linear_on"
  in go tele

let invert alpha ty sp t =
  if occurs_check alpha t then
    failwith "occurs check"
  else (* alpha does not occur in t *)
    match spine_to_tele sp with
    | Some xs when linear_on t xs ->
      let lam_tm = abstract_tm xs t in
      local (fun _ -> Emp) begin
        check ~ty lam_tm
      end >>= fun b ->
      ret @@ if b then Some lam_tm else None
    | _ ->
      (* Format.eprintf "Invert: nope %a @.@."
         (Tm.pp_spine Pretty.Env.emp) sp
         ; *)
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
  | Tm.Up (Tm.Meta alpha0, _), Tm.Up (Tm.Meta alpha1, _) ->
    Bwd.map snd <@> ask >>= fun gm ->
    begin
      popl >>= function
      | E (gamma, _, Hole `Rigid) as e when (alpha0 = gamma || alpha1 = gamma) ->
        pushls (e :: deps) >>
        block (Unify q)

      | E (gamma, _, Guess _) as e when (alpha0 = gamma || alpha1 = gamma) ->
        pushls (e :: deps) >>
        block (Unify q)

      | E (gamma, _, Hole `Flex) as e
        when
          (alpha0 = gamma || alpha1 = gamma)
          && Occurs.Set.mem gamma @@ Entries.free `Metas deps
        ->
        (* Format.eprintf "flex_flex_diff / popl / 1: %a %a at %a@." Name.pp alpha0 Name.pp alpha1 Name.pp gamma; *)
        pushls (e :: deps) >>
        block (Unify q)

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
    define Emp beta ~ty:ty' @@ f cmd
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
       tm0 = Tm.up (Tm.Meta alpha, sp0);
       tm1 = Tm.up (Tm.Meta alpha, sp1)}

let try_prune _q =
  (* TODO: implement pruning *)
  ret false


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
    | Tm.ExtLam _, Tm.ExtApp args ->
      let vargs = List.map (fun x -> T.Cx.unleash_dim T.Cx.emp @@ T.Cx.eval_dim T.Cx.emp x) args in
      let ty, _ = T.Cx.Eval.unleash_ext ty vargs in
      let vlam = T.Cx.eval T.Cx.emp tm in
      let vapp = T.Cx.Eval.ext_apply vlam vargs in
      T.Cx.quote T.Cx.emp ~ty vapp
    | Tm.Cons (t0, _), Tm.Car -> t0
    | Tm.Cons (_, t1), Tm.Cdr -> t1
    | Tm.LblRet t, Tm.LblCall -> t
    | Tm.Tt, Tm.If info -> info.tcase
    | Tm.Ff, Tm.If info -> info.fcase
    | _ -> failwith "TODO: plug"

  (* TODO: this sorry attempt results in things getting repeatedly evaluated *)
  let (%%) (ty, tm) frame =
    let vty = T.Cx.eval T.Cx.emp ty in
    let tm' = plug (vty, tm) frame in
    let vty' = T.infer_frame T.Cx.emp ~ty:vty ~hd:(T.Cx.eval T.Cx.emp tm) frame in
    let ty' = T.Cx.quote_ty T.Cx.emp vty' in
    ty', tm'
end

let push_guess gm ~ty0 ~ty1 tm  =
  let alpha = Name.fresh () in
  let ty0' = abstract_ty gm ty0 in
  let ty1' = abstract_ty gm ty1 in
  let tm' = abstract_tm gm tm in
  let hd = Tm.Meta alpha in
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
  let rec go sp0 sp1 =
    match sp0, sp1 with
    | Emp, Emp ->
      typechecker >>= fun (module T) ->
      let module HSubst = HSubst (T) in
      if x0 = x1 then
        lookup_var x0 tw0 >>= fun ty0 ->
        lookup_var x1 tw1 >>= fun ty1 ->
        let vty0 = T.Cx.eval T.Cx.emp ty0 in
        let vty1 = T.Cx.eval T.Cx.emp ty1 in
        ret (vty0, vty1)
      else
        begin
          Format.eprintf "rigid head mismatch: %a <> %a@." Name.pp x0 Name.pp x1;
          failwith "rigid head mismatch"
        end

    | Snoc (sp0, Tm.FunApp t0), Snoc (sp1, Tm.FunApp t1) ->
      go sp0 sp1 >>= fun (ty0, ty1) ->
      typechecker >>= fun (module T) ->
      let module HSubst = HSubst (T) in
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
      typechecker >>= fun (module T) ->
      let module HSubst = HSubst (T) in
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
      typechecker >>= fun (module T) ->
      let module HSubst = HSubst (T) in
      let dom0, _ = T.Cx.Eval.unleash_sg ~debug:["match-spine/car"] ty0 in
      let dom1, _ = T.Cx.Eval.unleash_sg ~debug:["match-spine/car"] ty1 in
      ret (dom0, dom1)

    | Snoc (sp0, Tm.Cdr), Snoc (sp1, Tm.Cdr) ->
      go sp0 sp1 >>= fun (ty0, ty1) ->
      typechecker >>= fun (module T) ->
      let module HSubst = HSubst (T) in
      let _, cod0 = T.Cx.Eval.unleash_sg ~debug:["match_spine/cdr"] ty0 in
      let _, cod1 = T.Cx.Eval.unleash_sg ~debug:["match-spine/cdr"] ty1 in
      let cod0 = T.Cx.Eval.inst_clo cod0 @@ T.Cx.eval_cmd T.Cx.emp (Tm.Ref (x0, tw0), sp0 #< Tm.Car) in
      let cod1 = T.Cx.Eval.inst_clo cod1 @@ T.Cx.eval_cmd T.Cx.emp (Tm.Ref (x1, tw1), sp1 #< Tm.Car) in
      ret (cod0, cod1)

    | Snoc (sp0, Tm.LblCall), Snoc (sp1, Tm.LblCall) ->
      go sp0 sp1 >>= fun (ty0, ty1) ->
      typechecker >>= fun (module T) ->
      let module HSubst = HSubst (T) in
      let _, _, ty0 = T.Cx.Eval.unleash_lbl_ty ty0 in
      let _, _, ty1 = T.Cx.Eval.unleash_lbl_ty ty1 in
      ret (ty0, ty1)

    | Snoc (sp0, Tm.If info0), Snoc (sp1, Tm.If info1) ->
      go sp0 sp1 >>= fun (_ty0, _ty1) ->
      typechecker >>= fun (module T) ->
      let module HSubst = HSubst (T) in
      let y = Name.fresh () in
      let mot0y = Tm.unbind_with y (fun _ -> `TwinL) info0.mot in
      let mot1y = Tm.unbind_with y (fun _ -> `TwinR) info1.mot in
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

    | Snoc (sp0, Tm.CoRForce), Snoc (sp1, Tm.CoRForce) ->
      go sp0 sp1

    | _ ->
      failwith "spine mismatch"

  in
  go sp0 sp1

let approx_sys _ty0 _ty1 _sys0 _sys1 =
  Format.eprintf "TODO!!!!@.";
  ret ()

let restriction_subtype ty0 sys0 ty1 sys1 =
  active @@ Subtype {ty0; ty1} >>
  approx_sys ty0 sys0 ty1 sys1



(* invariant: will not be called on inequations which are already reflexive *)
let rec subtype ty0 ty1 =
  if ty0 = ty1 then ret () else
    let univ = Tm.univ ~lvl:Lvl.Omega ~kind:Kind.Pre in
    match Tm.unleash ty0, Tm.unleash ty1 with
    | Tm.Pi (dom0, cod0), Tm.Pi (dom1, cod1) ->
      let x = Name.fresh () in
      let cod0x = Tm.unbind_with x (fun _ -> `TwinL) cod0 in
      let cod1x = Tm.unbind_with x (fun _ -> `TwinR) cod1 in
      active @@ Subtype {ty0 = dom1; ty1 = dom0} >>
      active @@ Problem.all_twins x dom0 dom1 @@ Subtype {ty0 = cod0x; ty1 = cod1x}

    | Tm.Sg (dom0, cod0), Tm.Sg (dom1, cod1) ->
      let x = Name.fresh () in
      let cod0x = Tm.unbind_with x (fun _ -> `TwinL) cod0 in
      let cod1x = Tm.unbind_with x (fun _ -> `TwinR) cod1 in
      active @@ Subtype {ty0 = dom0; ty1 = dom1} >>
      active @@ Problem.all_twins x dom0 dom1 @@ Subtype {ty0 = cod0x; ty1 = cod1x}

    | Tm.Ext ebnd0, Tm.Ext ebnd1 ->
      let xs, ty0, sys0 = Tm.unbind_ext ebnd0 in
      let xs_fwd = Bwd.to_list xs in
      let ty1, sys1 = Tm.unbind_ext_with xs_fwd ebnd1 in
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
          (* Format.eprintf "shoot??: %a <= %a@ / %a <= %a@." Tm.pp0 ty'0 Tm.pp0 ty'1 (Tm.pp_sys Pretty.Env.emp) sys0 (Tm.pp_sys Pretty.Env.emp) sys1; *)
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

    | Tm.Rst rst0, Tm.Rst rst1 ->
      restriction_subtype rst0.ty rst0.sys rst1.ty rst1.sys

    | Tm.Rst _, _ ->
      active @@ Subtype {ty0; ty1 = Tm.make @@ Tm.Rst {ty = ty1; sys = []}}

    | _ ->
      active @@ Problem.eqn ~ty0:univ ~ty1:univ ~tm0:ty0 ~tm1:ty1



(* invariant: will not be called on equations which are already reflexive *)
let rigid_rigid q =
  match Tm.unleash q.tm0, Tm.unleash q.tm1 with
  | Tm.Pi (dom0, cod0), Tm.Pi (dom1, cod1) ->
    let x = Name.named @@ Some "rigidrigid-pi" in
    let cod0x = Tm.unbind_with x (fun _ -> `TwinL) cod0 in
    let cod1x = Tm.unbind_with x (fun _ -> `TwinR) cod1 in
    active @@ Problem.eqn ~ty0:q.ty0 ~tm0:dom0 ~ty1:q.ty1 ~tm1:dom1 >>
    active @@ Problem.all_twins x dom0 dom1 @@
    Problem.eqn ~ty0:q.ty0 ~tm0:cod0x ~ty1:q.ty1 ~tm1:cod1x

  | Tm.Sg (dom0, cod0), Tm.Sg (dom1, cod1) ->
    let x = Name.named @@ Some "rigidrigid-sg" in
    let cod0x = Tm.unbind_with x (fun _ -> `TwinL) cod0 in
    let cod1x = Tm.unbind_with x (fun _ -> `TwinR) cod1 in
    active @@ Problem.eqn ~ty0:q.ty0 ~tm0:dom0 ~ty1:q.ty1 ~tm1:dom1 >>
    active @@ Problem.all_twins x dom0 dom1 @@
    Problem.eqn ~ty0:q.ty0 ~tm0:cod0x ~ty1:q.ty1 ~tm1:cod1x

  | Tm.Up (Tm.Ref (x0, tw0), sp0), Tm.Up (Tm.Ref (x1, tw1), sp1) ->
    match_spine x0 tw0 sp0 x1 tw1 sp1 >>
    ret ()

  | _ ->
    if is_orthogonal q then
      begin
        Format.eprintf "rigid-rigid mismatch: %a@." Equation.pp q;
        failwith "rigid-rigid mismatch"
      end
    else
      block @@ Unify q

let (%%) (ty, tm) frame =
  typechecker >>= fun (module T) ->
  let module HSubst = HSubst (T) in
  let open HSubst in
  ret @@ (ty, tm) %% frame


let unify q =
  match Tm.unleash q.ty0, Tm.unleash q.ty1 with
  | Tm.Pi (dom0, Tm.B (nm, _)), Tm.Pi (dom1, _) ->
    let x = Name.named nm in
    let x_l = Tm.up (Tm.Ref (x, `TwinL), Emp) in
    let x_r = Tm.up (Tm.Ref (x, `TwinR), Emp) in

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
    let xs = List.map Name.named nms0 in
    let vars = List.map (fun x -> Tm.up (Tm.Ref (x, `Only), Emp)) xs in
    let psi = List.map (fun x -> (x, `I)) xs in

    in_scopes psi
      begin
        (q.ty0, q.tm0) %% Tm.ExtApp vars >>= fun (ty0, tm0) ->
        (q.ty1, q.tm1) %% Tm.ExtApp vars >>= fun (ty1, tm1) ->
        ret @@ Problem.all_dims xs @@ Problem.eqn ~ty0 ~tm0 ~ty1 ~tm1
      end >>= fun prob ->
    active prob

  | Tm.Rst info0, Tm.Rst info1 ->
    active @@ Unify {q with ty0 = info0.ty; ty1 = info1.ty}

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


let rec split_sigma tele x ty =
  match Tm.unleash ty with
  | Tm.Sg (dom, Tm.B (_, cod)) ->
    let y = Name.fresh () in
    let z = Name.fresh () in
    let sp_tele = telescope_to_spine tele in

    let ytm = Tm.Ref (y, `Only), sp_tele in
    let ztm = Tm.Ref (z, `Only), sp_tele in
    let cody = Tm.subst (Tm.Sub (Tm.Id, ytm)) cod in

    Some
      ( y
      , abstract_ty tele dom
      , z
      , abstract_ty tele cody
      , abstract_tm tele @@ Tm.cons (Tm.up ytm) (Tm.up ztm)
      , ( abstract_tm tele @@ Tm.up (Tm.Ref (x, `Only), sp_tele #< Tm.Car)
        , abstract_tm tele @@ Tm.up (Tm.Ref (x, `Only), sp_tele #< Tm.Cdr)
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
    define tele alpha ~ty @@ Tm.make @@ Tm.LblRet (Tm.up t) >>
    ret true

  | Tm.Sg (dom, cod) ->
    hole `Flex tele dom @@ fun t0 ->
    (in_scopes (Bwd.to_list tele) typechecker) >>= fun (module T) ->
    let module HS = HSubst (T) in
    let vdom = T.Cx.eval T.Cx.emp dom in
    let cod' = HS.inst_ty_bnd cod (vdom, Tm.up t0) in
    hole `Flex tele cod' @@ fun t1 ->
    define tele alpha ~ty @@ Tm.cons (Tm.up t0) (Tm.up t1) >>
    ret true


  | Tm.Pi (dom, (Tm.B (nm, _) as cod)) ->
    let x = Name.named nm in
    begin
      match split_sigma Emp x dom with
      | None ->
        let codx = Tm.unbind_with x (fun _ -> `Only) cod in
        lower (tele #< (x, `P dom)) alpha codx

      | Some (y, ty0, z, ty1, s, (u, v)) ->
        let tele' = tele #< (y, `P ty0) #< (z, `P ty1) in
        (in_scopes (Bwd.to_list tele') typechecker) >>= fun (module T) ->
        let module HS = HSubst (T) in
        let vty = T.Cx.eval T.Cx.emp @@ abstract_ty tele dom in
        let pi_ty = abstract_ty (Emp #< (y, `P ty0) #< (z, `P ty1)) @@ HS.inst_ty_bnd cod (vty, s) in
        hole `Flex tele pi_ty @@ fun (whd, wsp) ->
        let bdy = Tm.up (whd, wsp #< (Tm.FunApp u) #< (Tm.FunApp v)) in
        define tele alpha ~ty @@ Tm.make @@ Tm.Lam (Tm.bind x bdy) >>
        ret true
    end

  | _ ->
    ret false

let is_reflexive q =
  let univ = Tm.univ ~lvl:Lvl.Omega ~kind:Kind.Pre in
  check_eq ~ty:univ q.ty0 q.ty1 >>= function
  | true ->
    check_eq ~ty:q.ty0 q.tm0 q.tm1
  | false ->
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
    check_subtype ty0 ty1 <||
    subtype ty0 ty1

  | All (param, prob) ->
    let x, probx = unbind param prob in
    if not (is_restriction param || Occurs.Set.mem x @@ Problem.free `Vars probx) then
      active probx
    else
      begin
        match param with
        | `I ->
          in_scope x `I @@
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

        | `Tw (ty0, ty1) ->
          let univ = Tm.univ ~lvl:Lvl.Omega ~kind:Kind.Pre in
          begin
            check_eq ~ty:univ ty0 ty1 >>= function
            | true ->
              get_global_env >>= fun sub ->
              let y = Name.named (Name.name x) in
              (*  This weird crap is needed to avoid creating a cycle in the environment.
                  What we should really do is kill 'twin variables' altogether and switch to
                  a representation based on having two contexts. *)
              let var_y = Tm.up (Tm.Ref (y, `Only), Emp) in
              let var_x = Tm.up (Tm.Ref (x, `Only), Emp) in
              let sub_y = Subst.define (Subst.ext sub y (`P {ty = ty0; sys = []})) x ~ty:ty0 ~tm:var_y in
              let sub_x = Subst.define (Subst.ext sub x (`P {ty = ty0; sys = []})) y ~ty:ty0 ~tm:var_x in
              solver @@ Problem.all x ty0 @@
              Problem.subst sub_x @@ Problem.subst sub_y probx
            | false ->
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
        | true ->
          (* Format.eprintf "solved guess %a??@." Name.pp alpha; *)
          pushl @@ E (alpha, ty, Defn info.tm) >>
          push_update alpha >>
          loop
        | false ->
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
