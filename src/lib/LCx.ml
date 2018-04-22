type t =
  {tys : Val.can Val.t list;
   env : Val.env;
   len : int}

let emp =
  {tys = [];
   env = Val.Env.emp;
   len = 0}

let ext cx v =
  {tys = v :: cx.tys;
   env = Val.Env.ext cx.env @@ Val.generic v @@ cx.len;
   len = cx.len + 1}

let def cx ~ty ~tm = 
  {tys = ty :: cx.tys;
   env = Val.Env.ext cx.env tm;
   len = cx.len + 1}

let proj cx = 
  {tys = List.tl cx.tys;
   env = Val.Env.proj cx.env;
   len = cx.len - 1}

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