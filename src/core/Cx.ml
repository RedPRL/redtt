open RedBasis open Bwd open BwdNotation
type value = Domain.value

type hyp = {classifier : [`Ty of value | `I]}

let check_eq_clock = ref 0.

let _ =
  Diagnostics.on_termination @@ fun _ ->
  Format.eprintf "[diagnostic]: Cx spent %fs in checking equality@." !check_eq_clock

(* The way that we model dimensions is now incompatible with the union-find version of things.
   We need to find a new way. *)
type cx =
  {sign : GlobalEnv.t;
   hyps : hyp bwd;
   env : Domain.env;
   qenv : Quote.env;
   ppenv : Pp.env;
   rel : Restriction.t}

type t = cx

let env cx = cx.env
let qenv cx = cx.qenv

let globals cx =
  cx.sign

let clear_locals cx =
  {cx with
   qenv = Quote.Env.emp;
   hyps = Emp;
   ppenv = Pp.Env.emp;
   env = Domain.Env.clear_locals cx.env}

let evaluator cx : (module Val.S) =
  let module Sig = struct let globals = cx.sign end in
  let module V = Val.M (GlobalEnv.M (Sig)) in
  (module V)

let ext cx ~nm ty sys =
  let n = Quote.Env.len cx.qenv in
  let (module V) = evaluator cx in
  let var = V.reflect ty (Domain.Lvl (nm, n)) sys in
  {cx with
   env = Domain.Env.snoc cx.env @@ `Val var;
   hyps = cx.hyps #< {classifier = `Ty ty};
   qenv = Quote.Env.succ cx.qenv;
   ppenv = snd @@ Pp.Env.bind cx.ppenv nm},
  var

let ext_ty cx ~nm ty =
  ext cx ~nm ty []

let def cx ~nm ~ty ~el =
  let face = Face.True (`Dim0, `Dim1, lazy el) in
  fst @@ ext cx ~nm ty [face]

let ext_dim cx ~nm =
  let x = Name.named nm in
  {cx with
   env = Domain.Env.snoc cx.env @@ `Dim (`Atom x);
   hyps = cx.hyps #< {classifier = `I};
   qenv = Quote.Env.abs cx.qenv [x];
   ppenv = snd @@ Pp.Env.bind cx.ppenv nm},
  x

let def_dim cx ~nm r =
  {cx with
   env = Domain.Env.snoc cx.env @@ `Dim r;
   hyps = cx.hyps #< {classifier = `I};
   qenv = Quote.Env.succ cx.qenv;
   ppenv = snd @@ Pp.Env.bind cx.ppenv nm}

let ext_dims cx ~nms =
  let xs = List.map Name.named nms in
  let rs = List.map (fun x -> `Atom x) xs in
  let rs_hyps = List.map (fun x -> {classifier = `I}) rs in
  {cx with
   env = Domain.Env.append cx.env @@ List.map (fun r -> `Dim r) rs;
   hyps = cx.hyps <>< rs_hyps;
   qenv = Quote.Env.abs cx.qenv xs;
   ppenv = snd @@ Pp.Env.bindn cx.ppenv nms},
  xs
let ppenv cx =
  cx.ppenv

let make_closure cx bnd =
  Domain.Clo {rho = cx.env; bnd}

let lookup i {hyps; _} =
  let hyp = Bwd.nth hyps i in
  hyp.classifier

let lookup_constant nm tw cx =
  GlobalEnv.lookup_ty cx.sign nm tw

let restrict cx r r' =
  (* WTF is this? weird, would be nice to delete. *)
  let phi = Restriction.as_action cx.rel in
  let r = I.act phi r in
  let r' = I.act phi r' in
  let rel, phi = Restriction.equate r r' cx.rel in
  let act_ty hyp =
    match hyp.classifier with
    | `Ty ty -> {classifier = `Ty (Domain.Value.act phi ty)}
    | `I -> hyp
  in
  let hyps = Bwd.map act_ty cx.hyps in
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

let eval_tm_sys cx sys =
  let (module V) = evaluator cx in
  V.eval_tm_sys cx.env sys

let quote cx ~ty el =
  let (module Q) = quoter cx in
  Q.quote_nf cx.qenv @@ {ty; el}

let quote_ty cx ty =
  let (module Q) = quoter cx in
  Q.quote_ty cx.qenv ty

let quote_dim cx r =
  let (module Q) = quoter cx in
  Q.quote_dim cx.qenv r

let check_eq cx ~ty el0 el1 =
  let (module Q) = quoter cx in
  let now0 = Unix.gettimeofday () in
  Q.equiv cx.qenv ~ty el0 el1;
  let now1 = Unix.gettimeofday () in
  check_eq_clock := !check_eq_clock +. (now1 -. now0)

let check_eq_ty cx el0 el1 =
  let (module Q) = quoter cx in
  Q.equiv_ty cx.qenv el0 el1

let check_eq_dim cx r0 r1 =
  let (module Q) = quoter cx in
  Q.equiv_dim cx.qenv r0 r1

let check_subtype cx ty0 ty1 =
  let (module Q) = quoter cx in
  Q.subtype cx.qenv ty0 ty1


let init globals =
  {sign = globals;
   env = Domain.Env.emp @@ GlobalEnv.global_dims globals;
   qenv = Quote.Env.emp;
   hyps = Emp;
   ppenv = Pp.Env.emp;
   rel = GlobalEnv.restriction globals}
