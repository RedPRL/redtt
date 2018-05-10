type atom = Symbol.t
type 'a abs = {atom : atom option; node : 'a}

module D = Dim

module type S =
sig
  type el

  include Sort.S with type 'a m = 'a with type t = el abs

  val bind : atom -> el -> t
  val const : el -> t
  val unleash : t -> atom * el
  val inst : t -> Dim.t -> el
end

module M (X : Sort.S with type 'a m = 'a) : S with type el = X.t =
struct
  type el = X.t
  type 'a m = 'a
  type t = X.t abs

  let unleash abs =
    match abs.atom with
    | None -> Symbol.fresh (), abs.node
    | Some a ->
      let x = Symbol.fresh () in
      x, X.act (D.swap x a) abs.node

  let inst abs r =
    match abs.atom with
    | None -> abs.node
    | Some a ->
      X.act (D.subst r a) abs.node

  (* FYI: It may not be necessary to freshen here, depending on how substitution is implemented. *)
  let bind atom node =
    let x = Symbol.fresh () in
    {atom = Some x; node = X.act (D.swap x atom) node}

  let const node =
    {atom = None; node = node}

  let act phi abs =
    let x, node = unleash abs in
    bind x @@ X.act phi node
end
