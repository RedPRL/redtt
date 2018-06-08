type atom = Name.t
type 'a abs = {atoms : atom list; node : 'a}

module D = Dim

module type S =
sig
  type el

  include Sort.S with type 'a m = 'a with type t = el abs

  val bind : atom list -> el -> t
  val unleash : t -> atom list * el
  val inst : t -> Dim.t list -> el

  val bind1 : atom -> el -> t
  val unleash1 : t -> atom * el
  val inst1 : t -> Dim.t -> el
end

module M (X : Sort.S with type 'a m = 'a) : S with type el = X.t =
struct
  type el = X.t
  type 'a m = 'a
  type t = X.t abs

  let rec freshen_atoms xs acc phi =
    match xs with
    | [] -> List.rev acc, phi
    | x :: xs ->
      let y = Name.named @@ Name.name x in
      freshen_atoms xs (y :: acc) @@
      D.cmp (D.swap y x) phi

  let unleash abs =
    let xs, phi = freshen_atoms abs.atoms [] D.idn in
    xs, X.act phi abs.node

  let rec inst_atoms xs rs phi =
    match xs, rs with
    | [], [] -> phi
    | x :: xs, r :: rs ->
      inst_atoms xs rs @@
      D.cmp phi @@ D.subst r x
    | _ -> failwith "inst_atoms"

  let inst abs rs =
    let phi = inst_atoms abs.atoms rs D.idn in
    X.act phi abs.node

  (* FYI: It may not be necessary to freshen here, depending on how substitution is implemented. *)
  let bind atoms node =
    {atoms; node}

  let bind1 x el =
    bind [x] el

  let unleash1 abs =
    let xs, el = unleash abs in
    match xs with
    | [x] -> x, el
    | _ -> failwith "unleash1: incorrect binding depth"

  let inst1 el r =
    inst el [r]

  let act phi abs =
    let xs, node = unleash abs in
    bind xs @@ X.act phi node
end
