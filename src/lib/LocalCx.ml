type hyp = [`Ty of Val2.value | `Dim]

let check_eq_clock = ref 0.

let _ =
  Diagnostics.on_termination @@ fun _ ->
  Format.eprintf "[diagnostic]: LocalCx spent %fs in checking equality@." !check_eq_clock

(* The way that we model dimensions is now incompatible with the union-find version of things.
   We need to find a new way. *)
type cx = {tys : hyp list; env : Val2.env; qenv : Quote2.env; ppenv : Pretty.env}
type t = cx

module type S =
sig
  type t = cx
  module Eval : Val2.S

  type value = Val2.value

  val emp : t

  val ext_ty : t -> nm:string option -> value -> t * value
  val ext_dim : t -> nm:string option -> t * I.atom
  val ext_dims : t -> nms:string option list -> t * I.atom list

  val restrict : t -> I.t -> I.t -> t

  val def : t -> nm:string option -> ty:value -> el:value -> t

  val ppenv : t -> Pretty.env
  val lookup : int -> t -> [`Ty of value | `Dim]

  val eval : t -> Tm.tm -> value
  val eval_cmd : t -> Tm.tm Tm.cmd -> value
  val eval_head : t -> Tm.tm Tm.head -> value
  val eval_frame : t -> value -> Tm.tm Tm.frame -> value
  val eval_dim : t -> Tm.tm -> I.t
  val eval_tm_sys : t -> (Tm.tm, Tm.tm) Tm.system -> Val2.val_sys

  val check_eq : t -> ty:value -> value -> value -> unit
  val check_subtype : t -> value -> value -> unit

  val quote : t -> ty:value -> value -> Tm.tm
  val quote_ty : t -> value -> Tm.tm

  val check_eq_ty : t -> value -> value -> unit
end


module M (V : Val2.S) : S =
struct
  type t = cx

  module Eval = V
  module Q = Quote2.M (V)

  type value = Val2.value

  let emp : cx =
    {env = [];
     qenv = Quote2.Env.emp;
     tys = [];
     ppenv = Pretty.Env.emp}

  let ext {env; qenv; tys; ppenv} ~nm ty sys =
    let n = Quote2.Env.len qenv in
    let var = V.reflect ty (Val2.Lvl (nm, n)) sys in
    {env = Val2.Val var :: env;
     tys = `Ty ty :: tys;
     qenv = Quote2.Env.succ qenv;
     ppenv = snd @@ Pretty.Env.bind nm ppenv},
    var

  let ext_ty cx ~nm ty =
    ext cx ~nm ty []

  let def cx ~nm ~ty ~el =
    let face = IFace.True (`Dim0, `Dim1, el) in
    fst @@ ext cx ~nm ty [face]

  let ext_dim {env; qenv; tys; ppenv} ~nm =
    let x = Name.named nm in
    {env = Val2.Atom (I.idn, x) :: env;
     tys = `Dim :: tys;
     qenv = Quote2.Env.abs qenv [x];
     ppenv = snd @@ Pretty.Env.bind nm ppenv}, x

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

  let eval_tm_sys {env; _} sys =
    V.eval_tm_sys env sys

  let lookup i {tys; _} =
    List.nth tys i

  let restrict cx r r' =
    {cx with env = V.Env.act (I.equate r r') cx.env}


  let quote cx ~ty el =
    Q.quote_nf cx.qenv @@ {ty; el}

  let quote_ty cx ty =
    Q.quote_ty cx.qenv ty


  let check_eq cx ~ty el0 el1 =
    let now0 = Unix.gettimeofday () in
    (* Format.eprintf "check_eq: %a = %a@." Eval.pp_value el0 Eval.pp_value el1 ; *)
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

