type atom = Symbol.t
type 'a abs = {atom : atom option; node : 'a}

module D = Dim

module M (X : Sort.S with type 'a m = 'a) :
sig
  include Sort.S with type 'a m = 'a with type t = X.t abs
  val bind : atom -> X.t -> t
  val const : X.t -> t
  val unleash : t -> atom * X.t
  val inst : t -> Dim.t -> X.t
end =
struct
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
