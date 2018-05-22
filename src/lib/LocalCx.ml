module type S =
sig
  type t
  type value = Val.value

  val emp : t

  val ext : t -> nm:string option -> value -> Val.val_sys -> t * value
  val ext_ty : t -> nm:string option -> value -> t * value
  val ext_dim : t -> nm:string option -> t * Val.atom
  val ext_dims : t -> nms:string option list -> t * Val.atom list

  val restrict : t -> Dim.repr -> Dim.repr -> t

  val def : t -> nm:string option -> ty:value -> el:value -> t

  val ppenv : t -> Pretty.env
  val lookup : int -> t -> [`Ty of value | `Dim]

  val eval : t -> 'a Tm.t -> value
  val eval_dim : t -> Tm.chk Tm.t -> Dim.repr
  val eval_tm_sys : t -> Tm.chk Tm.t Tm.system -> Val.val_sys

  val normalize : t -> ty:value -> tm:Tm.chk Tm.t -> Tm.chk Tm.t
  val normalize_tm_sys : t -> ty:value -> sys:Tm.chk Tm.t Tm.system -> Tm.chk Tm.t Tm.system

  val check_eq : t -> ty:value -> value -> value -> unit
  val check_subtype : t -> value -> value -> unit

  val quote : t -> ty:value -> value -> Tm.chk Tm.t
  val quote_ty : t -> value -> Tm.chk Tm.t

  val check_eq_ty : t -> value -> value -> unit

  val unleash_dim : t -> Dim.repr -> Dim.t
  val compare_dim : t -> Dim.repr -> Dim.repr -> Dim.compare
  val equate_dim : t -> Dim.repr -> Dim.repr -> Dim.action
end

type hyp = [`Ty of Val.value | `Dim]
module R = Restriction

(* The way that we model dimensions is now incompatible with the union-find version of things.
   We need to find a new way. *)
type cx = {tys : hyp list; env : Val.env; qenv : Quote.env; rel : R.t; ppenv : Pretty.env}
type t = cx


module M (V : Val.S) : S with type t = cx =
struct
  type t = cx
  module Q = Quote.M (V)

  type value = Val.value

  let emp : cx =
    {env = [];
     qenv = Quote.Env.emp;
     tys = [];
     ppenv = Pretty.Env.emp;
     rel = R.emp}

  let ext {env; qenv; tys; rel; ppenv} ~nm ty sys =
    let n = Quote.Env.len qenv in
    let var = V.make @@ Val.Up {ty; neu = Val.Lvl (nm, n); sys} in
    {env = Val.Val var :: env;
     tys = `Ty ty :: tys;
     qenv = Quote.Env.succ qenv;
     ppenv = snd @@ Pretty.Env.bind nm ppenv;
     rel},
    var

  let ext_ty cx ~nm ty =
    ext cx ~nm ty []

  let def cx ~nm ~ty ~el =
    let face = Face.True (Dim.dim0, Dim.dim0, el) in
    fst @@ ext cx ~nm ty [face]

  let ext_dim {env; qenv; tys; rel; ppenv} ~nm =
    let x = Symbol.named nm in
    {env = Val.Atom x :: env;
     tys = `Dim :: tys;
     qenv = Quote.Env.abs qenv [x];
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

  let eval {env; rel; ppenv; _} tm =
    try
      V.eval rel env tm
    with
    | exn ->
      Format.eprintf "Failed to evaluate: %a@." (Tm.pp ppenv) tm;
      raise exn

  let eval_dim {env; rel; _} tm =
    V.eval_dim rel env tm

  let eval_tm_sys {env; rel; _} sys =
    V.eval_tm_sys rel env sys

  let quote cx ~ty ~el =
    Q.quote_nf cx.qenv {ty; el}

  let normalize cx ~ty ~tm =
    quote cx ~ty ~el:(eval cx tm)

  let normalize_tm_sys cx ~ty ~sys =
    let vsys = eval_tm_sys cx sys in
    Q.quote_val_sys cx.qenv ty vsys

  let lookup i {tys; _} =
    List.nth tys i

  let restrict cx r r' =
    {cx with rel = R.equate r r' cx.rel}

  let equate_dim cx r r' =
    let cr = R.unleash r cx.rel in
    let cr' = R.unleash r' cx.rel in
    Dim.equate cr cr'

  let compare_dim cx r r' =
    R.compare r r' cx.rel

  let unleash_dim cx r =
    R.unleash r cx.rel


  let quote cx ~ty el =
    Q.quote_nf cx.qenv @@ {ty; el}

  let quote_ty cx ty =
    Q.quote_ty cx.qenv ty

  let check_eq cx ~ty el0 el1 =
    try
      Q.equiv cx.qenv ~ty el0 el1
    with
    | exn ->
      Format.eprintf "check_eq: %a /= %a@." V.pp_value el0 V.pp_value el1;
      raise exn

  let check_eq_ty cx el0 el1 =
    try
      Q.equiv_ty cx.qenv el0 el1
    with
    | exn ->
      Format.eprintf "check_eq_ty: %a /= %a@." V.pp_value el0 V.pp_value el1;
      raise exn

  let check_subtype cx ty0 ty1 =
    try
      Q.subtype cx.qenv ty0 ty1
    with
    | exn ->
      Format.eprintf "subtype: %a /<= %a@." V.pp_value ty0 V.pp_value ty1;
      raise exn

end
