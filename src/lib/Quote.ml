open Val

let generic n ty =
  into @@ Up {ty = ty; neu = Lvl n}

module Rel :
sig
  type 'a t
  val refl : 'a -> 'a t
  val equ : 'a -> 'a -> 'a t
  val get : 'a t -> 'a

  val apply : value t -> value -> value t
  val car : value t -> value t
  val cdr : value t -> value t
end =
struct
  type 'a t =
    | Refl of 'a
    | Equ of 'a * 'a

  let refl v = Refl v
  let equ v0 v1 = Equ (v0, v1)

  let get rel =
    match rel with
    | Refl v -> v
    | Equ (v, _) -> v

  let apply rel v =
    match rel with
    | Refl vfun ->
      Refl (Val.apply vfun v)
    | Equ (vfun0, vfun1) ->
      Equ (Val.apply vfun0 v, Val.apply vfun1 v)

  let car rel =
    match rel with
    | Refl v ->
      Refl (Val.car v)
    | Equ (v0, v1) ->
      Equ (Val.car v0, Val.car v1)

  let cdr rel =
    match rel with
    | Refl v ->
      Refl (Val.cdr v)
    | Equ (v0, v1) ->
      Equ (Val.cdr v0, Val.cdr v1)
end

module Generalized :
sig
  val quote : int -> value -> value Rel.t -> Tm.chk Tm.t
  val quote_neu : int -> neu Rel.t -> Tm.inf Tm.t
end =
struct
  let rec quote n ty el =
    match unleash ty with
    | Pi {dom; cod} ->
      let var = generic n dom in
      let vcod = inst_clo cod var in
      let app = Rel.apply el var in
      Tm.lam None @@
      quote (n + 1) vcod app

    | Sg {dom; cod} ->
      let el0 = Rel.car el in
      let q0 = quote n dom el0 in
      let vcod = inst_clo cod @@ Rel.get el0 in
      let q1 = quote n vcod @@ Rel.cdr el in
      Tm.cons q0 q1

    | _ ->
      failwith ""

  and quote_neu _n _el =
    failwith ""

end

let quote_nf n nf =
  Generalized.quote n nf.ty @@ Rel.refl nf.el

let quote_neu n neu =
  Generalized.quote_neu n @@ Rel.refl neu

let equiv n ~ty el0 el1 =
  match Generalized.quote n ty @@ Rel.equ el0 el1 with
  | _ ->
    true
  | exception _ ->
    false
