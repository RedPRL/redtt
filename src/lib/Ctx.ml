module D = Val

type t = {len : int; tys : D.d list; vals: D.d list}

let define ~ctx ~ty ~tm =
  {len = ctx.len + 1;
    tys = ty :: ctx.tys;
    vals = tm :: ctx.vals}

let add ~ctx ~ty =
  let tm = D.Up (ty, D.Atom ctx.len) in
  define ~ctx ~ty ~tm, tm

let env ~ctx = ctx.vals
let tys ~ctx = ctx.tys

let len ~ctx = ctx.len

let lookup_lvl ~ctx ~lvl = 
  let ix = ctx.len - (lvl + 1) in
  List.nth ctx.tys ix, List.nth ctx.vals ix