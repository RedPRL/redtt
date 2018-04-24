type t =
  {tys : Val.can Val.t list;
   env : Val.env;
   ppenv : Pretty.Env.t;
   len : int}

let emp =
  {tys = [];
   env = Val.Env.emp;
   ppenv = Pretty.Env.emp;
   len = 0}

let ext cx ?nm:(nm = None) v =
  let _, ppenv = Pretty.Env.bind nm cx.ppenv in
  {tys = v :: cx.tys;
   env = Val.Env.ext cx.env @@ Val.generic v @@ cx.len;
   len = cx.len + 1;
   ppenv}

let def cx ?nm:(nm = None) ty tm = 
  let _, ppenv = Pretty.Env.bind nm cx.ppenv in
  {tys = ty :: cx.tys;
   env = Val.Env.ext cx.env tm;
   len = cx.len + 1;
   ppenv}

let proj_exn cx = 
  let ppenv = Pretty.Env.proj cx.ppenv in
  {tys = List.tl cx.tys;
   env = fst @@ Val.Env.proj cx.env;
   len = cx.len - 1;
   ppenv}


type view = 
  | Snoc of {cx : t; ty : Val.can Val.t; def : Val.can Val.t}
  | Nil

let view cx = 
  match cx.tys with
  | [] ->
    Nil

  | ty :: _tys ->
    let cx' = proj_exn cx in
    Snoc {cx = cx'; ty = ty; def = snd @@ Val.Env.proj cx.env }


let proj cx = 
  try Some (proj_exn cx) with
  | _ -> None

let restrict_exn cx d0 d1 =
  let env = Val.Env.restrict_exn cx.env d0 d1 in
  {cx with env = env}

let compare_dim cx =
  Val.Env.compare_dim cx.env

let canonize cx = 
  Val.Env.canonize cx.env

exception Inconsistent = DimRel.Inconsistent

let lookup i cx =
  List.nth cx.tys i

let len cx = cx.len
let env cx = cx.env 
let ppenv cx = cx.ppenv