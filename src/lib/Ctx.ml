type t = {len : int; tys : Val.can Val.t list; vals: Val.can Val.t list}

let emp = 
  {len = 0;
   tys = [];
   vals = []}

let define ~ctx ~ty ~tm =
  {len = ctx.len + 1;
   tys = ty :: ctx.tys;
   vals = tm :: ctx.vals}

let add ~ctx ~ty =
  let tm = Val.into @@ Val.Up (ty, Val.into @@ Val.Lvl ctx.len) in
  define ~ctx ~ty ~tm, tm

let env ~ctx = ctx.vals
let tys ~ctx = ctx.tys

let len ~ctx = ctx.len

let lookup_lvl ~ctx ~lvl = 
  let ix = ctx.len - (lvl + 1) in
  List.nth ctx.tys ix, List.nth ctx.vals ix