module V = Val
module Q = Quote
module R = Restriction

type value = V.value

type hyp = [`Ty of value | `Dim]

(* The way that we model dimensions is now incompatible with the union-find version of things.
   We need to find a new way. *)
type t = {tys : hyp list; env : V.env; qenv : Q.env; rel : R.t; ppenv : Pretty.env}

let emp =
  {env = [];
   qenv = Q.Env.emp;
   tys = [];
   ppenv = Pretty.Env.emp;
   rel = R.emp}

let ext_ty {env; qenv; tys; rel; ppenv} ~nm vty =
  let n = Q.Env.len qenv in
  let var = V.make @@ V.Up {ty = vty; neu = V.Lvl (nm, n)} in
  {env = V.Val var :: env;
   tys = `Ty vty :: tys;
   qenv = Q.Env.succ qenv;
   ppenv = snd @@ Pretty.Env.bind nm ppenv;
   rel},
  var

let def {env; qenv; tys; rel; ppenv} ~nm ~ty ~el =
  {env = V.Val el :: env;
   tys = `Ty ty :: tys;
   qenv = Q.Env.succ qenv; (* Is this right? *)
   ppenv = snd @@ Pretty.Env.bind nm ppenv;
   rel}

let ext_dim {env; qenv; tys; rel; ppenv} ~nm =
  let x = Symbol.named nm in
  {env = V.Atom x :: env;
   tys = `Dim :: tys;
   qenv = Q.Env.abs qenv [x];
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
  Q.quote_nf cx.qenv @@ V.{ty; el}

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
