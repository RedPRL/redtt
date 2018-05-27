open RedBasis
open Bwd open BwdNotation
open Contextual
open Dev

module Notation = Monad.Notation (Contextual)
open Notation

type telescope = (Name.t * ty) list

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
  Tm.FunApp (Tm.up @@ Tm.Cut (Tm.Ref (x, `Only), Emp))

let hole gm ty f =
  let alpha = Name.fresh () in
  pushl (E (alpha, pis gm ty, Hole)) >>
  let hd = Tm.Meta alpha in
  let sp = telescope_to_spine gm in
  f (hd, sp) >>= fun r ->
  go_left >>
  ret r

let define gm alpha ty tm =
  let ty' = pis gm ty in
  let tm' = lambdas (Bwd.map fst gm) tm in
  (* In Gundry/McBride, a substitution is also unleashed to the right. We're going to find out if we need it. *)
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
      | Tm.Up (Tm.Cut (Tm.Ref (f, twf), Snoc (sp, Tm.FunApp arg))) ->
        begin
          match Tm.unleash arg with
          | Tm.Up (Tm.Cut (Tm.Ref (y', _), Emp))
            when
              y = y'
              && not @@ Occurs.Set.mem y @@ Tm.Sp.free `Vars sp
            ->
            Tm.up @@ Tm.Cut (Tm.Ref (f, twf), sp)
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
      | Tm.Up (Tm.Cut (hd0, Snoc (sp0, Tm.Car))), Tm.Up (Tm.Cut (hd1, Snoc (sp1, Tm.Cdr)))
        when
          hd0 = hd1 && sp0 = sp1
        ->
        Tm.up @@ Tm.Cut (hd0, sp0)
      | _ ->
        Tm.cons t0' t1'
    end

  | con ->
    Tm.make @@ Tm.map_tmf eta_contract con

let to_var t =
  match Tm.unleash @@ eta_contract t with
  | Tm.Up (Tm.Cut (Tm.Ref (a, _), Emp)) ->
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
  | Tm.Up (Tm.Cut (Meta alpha, sp)) ->
    begin
      invert alpha ty sp q.tm1 >>= function
      | None ->
        ret false
      | Some t ->
        active (Unify q) >>
        define Emp alpha ty t >>
        ret true
    end
  | _ ->
    failwith "try_invert"

let rec flex_term ~deps q =
  match Tm.unleash q.tm0 with
  | Tm.Up (Tm.Cut (Meta alpha, _)) ->
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
  | Tm.Up (Tm.Cut (Tm.Meta alpha0, _)), Tm.Up (Tm.Cut (Tm.Meta alpha1, _)) ->
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

type instantiation = Name.t * ty * (tm -> tm)

let rec instantiate inst =
  let alpha, ty, f = inst in
  popl >>= function
  | E (beta, ty', Hole) when alpha = beta ->
    hole Emp ty @@ fun t ->
    define Emp beta ty' @@ f t
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
      Tm.up @@ Tm.Cut (hd, sp <.> sp')
    in
    instantiate (alpha, pis tele' cod, f)
  | None ->
    block @@ Unify
      {q with
       tm0 = Tm.up @@ Tm.Cut (Tm.Meta alpha, sp0);
       tm1 = Tm.up @@ Tm.Cut (Tm.Meta alpha, sp1)}

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
  let rec inst_bnd (ty_clo, tm_bnd) (arg_ty, arg) =
    let Tm.B (nm, tm) = tm_bnd in
    let varg = T.Cx.eval T.Cx.emp arg in
    let lcx = T.Cx.def T.Cx.emp ~nm ~ty:arg_ty ~el:varg in
    let el = T.Cx.eval lcx tm in
    let vty = T.Cx.Eval.inst_clo ty_clo varg in
    T.Cx.quote T.Cx.emp ~ty:vty el

  and plug (ty, tm) frame =
    let rec unleash_ty ty =
      match T.Cx.Eval.unleash ty with
      | Val.Rst info -> unleash_ty info.ty
      | con -> con
    in
    match Tm.unleash tm, unleash_ty ty, frame with
    | Tm.Up (Tm.Cut (hd, sp)), _, _ ->
      Tm.up @@ Tm.Cut (hd, sp #< frame)
    | Tm.Lam bnd, Val.Pi {dom; cod}, Tm.FunApp arg ->
      inst_bnd (cod, bnd) (dom, arg)
    | _, _, Tm.ExtApp _ ->
      failwith "TODO: %%/ExtApp"
    | Tm.Cons (t0, _), _, Tm.Car -> t0
    | Tm.Cons (_, t1), _, Tm.Cdr -> t1
    | Tm.LblRet t, _, Tm.LblCall -> t
    | Tm.Tt, _, Tm.If info -> info.tcase
    | Tm.Ff, _, Tm.If info -> info.fcase
    | _ -> failwith "TODO: %%"

  let (%%) (ty, tm) frame =
    let vty = T.Cx.eval T.Cx.emp ty in
    let tm' = plug (vty, tm) frame in
    let el = T.Cx.eval T.Cx.emp tm' in
    let vty' = T.infer_frame T.Cx.emp ~ty:vty ~hd:el frame in
    let ty' = T.Cx.quote_ty T.Cx.emp vty' in
    ty', tm'
end


let rigid_rigid _q =
  failwith "TODO: rigid_rigid"

let unify q =
  typechecker >>= fun (module T) ->
  let module HS = HSubst (T) in
  let open HS in

  match Tm.unleash q.ty0, Tm.unleash q.ty1 with
  | Tm.Pi (dom0, _), Tm.Pi (dom1, _) ->
    let x = Name.fresh () in
    let x_l = Tm.up @@ Tm.Cut (Tm.Ref (x, `TwinL), Emp) in
    let x_r = Tm.up @@ Tm.Cut (Tm.Ref (x, `TwinR), Emp) in
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
    | Tm.Up (Tm.Cut (Tm.Meta alpha0, sp0)), Tm.Up (Tm.Cut (Tm.Meta alpha1, sp1))
      when
        alpha0 = alpha1
      ->
      try_prune q <|| begin
        try_prune (Equation.sym q) <||
        flex_flex_same {q with tm0 = alpha0, sp0; tm1 = sp1}
      end

    | Tm.Up (Tm.Cut (Tm.Meta _, _)), Tm.Up (Tm.Cut (Tm.Meta _, _)) ->
      try_prune q <|| begin
        try_prune (Equation.sym q) <||
        flex_flex_diff [] q
      end

    | Tm.Up (Tm.Cut (Tm.Meta _, _)), _ ->
      try_prune q <|| flex_term [] q

    | _, Tm.Up (Tm.Cut (Tm.Meta _, _)) ->
      let q' = Equation.sym q in
      try_prune q' <|| flex_term [] q'

    | _ ->
      rigid_rigid q
