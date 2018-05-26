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
      | Tm.Up (Tm.Cut (Tm.Ref f, Snoc (sp, Tm.FunApp arg))) ->
        begin
          match Tm.unleash arg with
          | Tm.Up (Tm.Cut (Tm.Ref y', Emp))
            when
              y = y'
              && not @@ Occurs.Set.mem y @@ Tm.Sp.free `Vars sp
            ->
            Tm.up @@ Tm.Cut (Tm.Ref f, sp)
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
  | Tm.Up (Tm.Cut (Tm.Ref a, Emp)) ->
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

let invert alpha _ty sp t =
  if occurs_check alpha t then
    failwith "occurs check"
  else (* alpha does not occur in t *)
    match spine_to_vars sp with
    | Some xs when linear_on t xs ->
      let lam_tm = lambdas xs t in
      local (fun _ -> Emp) begin
        (* TODO: typecheck (lam xs ... t) *)
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

let flex_flex_same q =
  match Tm.unleash q.tm0, Tm.unleash q.tm1 with
  (* invariant: same alpha *)
  | Tm.Up (Tm.Cut (Tm.Meta alpha, sp0)), Tm.Up (Tm.Cut (Tm.Meta _, sp1)) ->
    lookup_meta alpha >>= fun ty_alpha ->
    let tele, _cod = telescope ty_alpha in
    begin
      match intersect tele sp0 sp1 with
      | Some _ ->
        failwith "TODO"
      | None ->
        block @@ Unify q
    end
  | _ -> failwith ""
