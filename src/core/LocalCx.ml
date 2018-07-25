open RedBasis.Bwd
open BwdNotation

type value = Domain.value

type hyp =
  {classifier : [`Ty of value | `I | `Tick];
   killed : bool; (* for modal calculus *)
   locks : int (* for modal calculus *)
  }

let check_eq_clock = ref 0.

let _ =
  Diagnostics.on_termination @@ fun _ ->
  Format.eprintf "[diagnostic]: LocalCx spent %fs in checking equality@." !check_eq_clock

(* The way that we model dimensions is now incompatible with the union-find version of things.
   We need to find a new way. *)
type cx = {hyps : hyp list; env : Domain.env; qenv : Quote.env; ppenv : Pretty.env; rel : Restriction.t}
type t = cx

let clear_locals cx =
  {cx with
   qenv = Quote.Env.emp;
   hyps = [];
   ppenv = Pretty.Env.emp;
   env = Domain.Env.clear_locals cx.env}

let hyp_map_lock f hyp =
  {hyp with locks = f hyp.locks}


let ext_lock cx =
  {cx with hyps = List.map (hyp_map_lock (fun n -> n + 1)) cx.hyps}

let clear_locks cx =
  {cx with hyps = List.map (hyp_map_lock (fun _ -> 0)) cx.hyps}

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
  | `Global _ ->
    failwith "TODO: implement kill_from_tick for global tick"

let ext {env; qenv; hyps; ppenv; rel} ~nm ty sys =
  let n = Quote.Env.len qenv in
  let var = Domain.Node {con = Domain.Reflect {ty; neu = Domain.Lvl (nm, n); sys}; action = I.idn} in
  {env = Domain.Env.push (Domain.Val var) env;
   hyps = {classifier = `Ty ty; locks = 0; killed = false} :: hyps;
   qenv = Quote.Env.succ qenv;
   ppenv = snd @@ Pretty.Env.bind nm ppenv;
   rel},
  var

let ext_tick {env; qenv; hyps; ppenv; rel} ~nm =
  let n = Quote.Env.len qenv in
  let tick = Domain.TickGen (`Lvl (nm, n)) in
  {env = Domain.Env.push (Domain.Tick tick) env;
   hyps = {classifier = `Tick; locks = 0; killed = false} :: hyps;
   qenv = Quote.Env.succ qenv;
   ppenv = snd @@ Pretty.Env.bind nm ppenv;
   rel},
  tick

let ext_ty cx ~nm ty =
  ext cx ~nm ty []

let def cx ~nm ~ty ~el =
  let face = Face.True (`Dim0, `Dim1, el) in
  fst @@ ext cx ~nm ty [face]

let ext_dim {env; qenv; hyps; ppenv; rel} ~nm =
  let x = Name.named nm in
  {env = Domain.Env.push (Domain.Atom (`Atom x)) env;
   hyps = {classifier = `I; locks = 0; killed = false} :: hyps;
   qenv = Quote.Env.abs qenv @@ Emp #< x;
   ppenv = snd @@ Pretty.Env.bind nm ppenv;
   rel}, x

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
  let {classifier; locks; killed} = List.nth hyps i in
  if (killed || locks > 0) && classifier != `I then
    failwith "Hypothesis is inaccessible (modal, taste it!)"
  else
    classifier

let restrict cx r r' =
  let phi = Restriction.as_action cx.rel in
  let r = I.act phi r in
  let r' = I.act phi r' in
  let rel, phi = Restriction.equate r r' cx.rel in
  let act_ty {classifier; locks; killed} =
    match classifier with
    | `Ty ty -> {classifier = `Ty (Domain.Value.act phi ty); locks; killed}
    | `I -> {classifier = `I; locks; killed}
    | `Tick -> {classifier = `Tick; locks; killed}
  in
  let hyps = List.map act_ty cx.hyps in
  let env = Domain.Env.act phi cx.env in
  {cx with rel; hyps; env}, phi



module type S =
sig
  type t = cx
  module Eval : Val.S

  val emp : t

  val eval : t -> Tm.tm -> value
  val eval_cmd : t -> Tm.tm Tm.cmd -> value
  val eval_head : t -> Tm.tm Tm.head -> value
  val eval_frame : t -> value -> Tm.tm Tm.frame -> value
  val eval_dim : t -> Tm.tm -> I.t
  val eval_tick : t -> Tm.tm -> Domain.tick
  val eval_tm_sys : t -> (Tm.tm, Tm.tm) Tm.system -> Domain.val_sys

  val check_eq : t -> ty:value -> value -> value -> unit
  val check_subtype : t -> value -> value -> unit

  val quote : t -> ty:value -> value -> Tm.tm
  val quote_ty : t -> value -> Tm.tm

  val check_eq_ty : t -> value -> value -> unit
end


module M (V : Val.S) : S =
struct
  type t = cx

  module Eval = V

  let emp : cx =
    {env = Domain.Env.emp;
     qenv = Quote.Env.emp;
     hyps = [];
     ppenv = Pretty.Env.emp;
     rel = V.base_restriction}

  let eval {env; ppenv; _} tm =
    try
      V.eval env tm
    with
    | exn ->
      Format.eprintf "Failed to evaluate: %a because of %s@." (Tm.pp ppenv) tm (Printexc.to_string exn);
      raise exn

  let eval_cmd {env; ppenv; _} cmd =
    try
      V.eval_cmd env cmd
    with
    | exn ->
      Format.eprintf "Failed to evaluate: %a@." (Tm.pp_cmd ppenv) cmd;
      raise exn

  let eval_frame {env; _} frm hd =
    V.eval_frame env frm hd

  let eval_head {env; ppenv; _} hd =
    try
      V.eval_head env hd
    with
    | exn ->
      Format.eprintf "Failed to evaluate: %a@." (Tm.pp_head ppenv) hd;
      raise exn

  let eval_dim {env; _} tm =
    V.eval_dim env tm

  let eval_tick {env; _} tm =
    V.eval_tick env tm

  let eval_tm_sys {env; _} sys =
    V.eval_tm_sys env sys


  module Q = Quote.M (V)

  let quote cx ~ty el =
    Q.quote_nf cx.qenv @@ {ty; el}

  let quote_ty cx ty =
    Q.quote_ty cx.qenv ty


  let check_eq cx ~ty el0 el1 =
    let now0 = Unix.gettimeofday () in
    try
      Q.equiv cx.qenv ~ty el0 el1;
      let now1 = Unix.gettimeofday () in
      check_eq_clock := !check_eq_clock +. (now1 -. now0)
    with
    | exn ->
      (* Format.eprintf "check_eq: %a /= %a@." V.pp_value el0 V.pp_value el1; *)
      raise exn

  let check_eq_ty cx el0 el1 =
    try
      Q.equiv_ty cx.qenv el0 el1
    with
    | exn ->
      (* Format.eprintf "check_eq_ty: %a /= %a@." V.pp_value el0 V.pp_value el1; *)
      raise exn

  let check_subtype cx ty0 ty1 =
    try
      Q.subtype cx.qenv ty0 ty1
    with
    | exn ->
      (* Format.eprintf "subtype: %a /<= %a@." V.pp_value ty0 V.pp_value ty1; *)
      raise exn

end

