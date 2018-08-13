open RedBasis.Bwd
open BwdNotation

type value = Domain.value

type hyp =
  {classifier : [`Ty of value | `I | `Tick];
   killed : bool; (* for modal calculus *)
   locked : bool (* for modal calculus *)
  }

let check_eq_clock = ref 0.

let _ =
  Diagnostics.on_termination @@ fun _ ->
  Format.eprintf "[diagnostic]: Cx spent %fs in checking equality@." !check_eq_clock

(* The way that we model dimensions is now incompatible with the union-find version of things.
   We need to find a new way. *)
type cx =
  {sign : GlobalEnv.t;
   hyps : hyp list;
   env : Domain.env;
   qenv : Quote.env;
   ppenv : Pp.env;
   rel : Restriction.t;
   all_locks : int}

type t = cx

let env cx = cx.env
let qenv cx = cx.qenv

let globals cx =
  cx.sign

let clear_locals cx =
  {cx with
   qenv = Quote.Env.emp;
   hyps = [];
   ppenv = Pp.Env.emp;
   env = Domain.Env.clear_locals cx.env;
   all_locks = 0}
let ext_lock cx =
  {cx with
   sign = GlobalEnv.ext_lock cx.sign;
   hyps = List.map (fun hyp -> {hyp with locked = true}) cx.hyps;
   all_locks = cx.all_locks + 1}

let hyps_clear_locks hyps =
  let rec go hyps =
    match hyps with
    | [] -> []
    | hyp :: hyps ->
      match hyp.classifier with
      | `Tick -> hyp :: hyps (* Maybe not quite right *)
      | _ ->
        {hyp with locked = false} :: go hyps
  in
  go hyps

let clear_locks cx =
  {cx with
   sign = GlobalEnv.clear_locks cx.sign;
   hyps = hyps_clear_locks cx.hyps;
   all_locks = 0}

let kill_from_tick cx tgen =
  match tgen with
  | `Lvl (_, lvl) ->
    let i = Quote.Env.len cx.qenv - lvl - 1 in
    let go j hyp =
      if j <= i then
        {hyp with killed = true}
      else
        hyp
    in
    {cx with hyps = List.mapi go cx.hyps}
  | `Global alpha ->
    {cx with sign = GlobalEnv.kill_from_tick cx.sign alpha}

let evaluator cx : (module Val.S) =
  let module Sig = struct let globals = cx.sign end in
  let module V = Val.M (GlobalEnv.M (Sig)) in
  (module V)

let ext cx ~nm ty sys =
  let n = Quote.Env.len cx.qenv in
  let (module V) = evaluator cx in
  let var = V.reflect ty (Domain.Lvl (nm, n)) sys in
  {cx with
   env = Domain.Env.push (`Val var) cx.env;
   hyps = {classifier = `Ty ty; locked = false; killed = false} :: cx.hyps;
   qenv = Quote.Env.succ cx.qenv;
   ppenv = snd @@ Pp.Env.bind nm cx.ppenv},
  var

let ext_tick cx ~nm =
  let n = Quote.Env.len cx.qenv in
  let tick = Domain.TickGen (`Lvl (nm, n)) in
  {cx with
   env = Domain.Env.push (`Tick tick) cx.env;
   hyps = {classifier = `Tick; locked = false; killed = false} :: cx.hyps;
   qenv = Quote.Env.succ cx.qenv;
   ppenv = snd @@ Pp.Env.bind nm cx.ppenv},
  tick

let ext_ty cx ~nm ty =
  ext cx ~nm ty []

let def cx ~nm ~ty ~el =
  let face = Face.True (`Dim0, `Dim1, lazy el) in
  fst @@ ext cx ~nm ty [face]

let ext_dim cx ~nm =
  let x = Name.named nm in
  {cx with
   env = Domain.Env.push (`Dim (`Atom x)) cx.env;
   hyps = {classifier = `I; locked = false; killed = false} :: cx.hyps;
   qenv = Quote.Env.abs cx.qenv @@ Emp #< x;
   ppenv = snd @@ Pp.Env.bind nm cx.ppenv},
  x

let rec ext_dims cx ~nms =
  match nms with
  | [] -> cx, []
  | nm::nms ->
    (* TODO: is this backwards? *)
    let cx, xs = ext_dims cx ~nms in
    let cx, x = ext_dim cx ~nm in
    cx, x :: xs

let ppenv cx =
  cx.ppenv

let make_closure cx bnd =
  Domain.Clo {rho = cx.env; bnd}

let lookup i {hyps; _} =
  let hyp = try List.nth hyps i with _ -> failwith "Cx.lookup out of range" in
  if (hyp.killed || hyp.locked) && hyp.classifier != `I then
    failwith "Hypothesis is inaccessible"
  else
    hyp.classifier

let lookup_constant nm tw cx =
  (* For constants, the only locks that are relevant are the global ones. Ignore the local locks. *)
  GlobalEnv.lookup_ty cx.sign nm tw

let restrict cx r r' =
  let phi = Restriction.as_action cx.rel in
  let r = I.act phi r in
  let r' = I.act phi r' in
  let rel, phi = Restriction.equate r r' cx.rel in
  let act_ty hyp =
    match hyp.classifier with
    | `Ty ty -> {hyp with classifier = `Ty (Domain.Value.act phi ty)}
    | `I -> hyp
    | `Tick -> hyp
  in
  let hyps = List.map act_ty cx.hyps in
  let env = Domain.Env.act phi cx.env in
  {cx with rel; hyps; env}, phi



let quoter cx : (module Quote.S) =
  let (module V) = evaluator cx in
  let module Q = Quote.M (V) in
  (module Q)

let eval cx tm =
  let (module V) = evaluator cx in
  V.eval cx.env tm

let eval_cmd cx cmd =
  let (module V) = evaluator cx in
  V.eval_cmd cx.env cmd

let eval_frame cx frm hd =
  let (module V) = evaluator cx in
  V.eval_frame cx.env frm hd

let eval_head cx hd =
  let (module V) = evaluator cx in
  V.eval_head cx.env hd

let eval_dim cx tm =
  let (module V) = evaluator cx in
  V.eval_dim cx.env tm

let eval_tick cx tm =
  let (module V) = evaluator cx in
  V.eval_tick cx.env tm

let eval_tm_sys cx sys =
  let (module V) = evaluator cx in
  V.eval_tm_sys cx.env sys

let quote cx ~ty el =
  let (module Q) = quoter cx in
  Q.quote_nf cx.qenv @@ {ty; el}

let quote_ty cx ty =
  let (module Q) = quoter cx in
  Q.quote_ty cx.qenv ty


let check_eq cx ~ty el0 el1 =
  let (module Q) = quoter cx in
  let now0 = Unix.gettimeofday () in
  Q.equiv cx.qenv ~ty el0 el1;
  let now1 = Unix.gettimeofday () in
  check_eq_clock := !check_eq_clock +. (now1 -. now0)

let check_eq_ty cx el0 el1 =
  let (module Q) = quoter cx in
  Q.equiv_ty cx.qenv el0 el1

let check_subtype cx ty0 ty1 =
  let (module Q) = quoter cx in
  Q.subtype cx.qenv ty0 ty1


let init globals =
  {sign = globals;
   env = Domain.Env.emp;
   qenv = Quote.Env.emp;
   hyps = [];
   ppenv = Pp.Env.emp;
   rel = GlobalEnv.restriction globals;
   all_locks = 0}
