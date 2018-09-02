open RedBasis.Bwd
open BwdNotation

type atom = Name.t
type 'a abs = {atoms : atom bwd; node : 'a}

let pp ih fmt {atoms; node} =
  let pp_atoms fmt atoms =
    let pp_sep fmt () = Format.fprintf fmt " " in
    Format.pp_print_list ~pp_sep Name.pp fmt (Bwd.to_list atoms)
  in
  Format.fprintf fmt "@[<hv1><%a>@ %a@]"
    pp_atoms atoms
    ih node

module type S =
sig
  type el

  include Sort.S with type 'a m = 'a with type t = el abs

  val unsafe_map : (el -> el) -> t -> t

  val unsafe_bind : atom bwd -> el -> t
  val bind : atom bwd -> el -> t
  val unleash : t -> atom bwd * el
  val inst : t -> I.t bwd -> el

  val len : t -> int

  val unsafe_bind1 : atom -> el -> t
  val bind1 : atom -> el -> t
  val unleash1 : t -> atom * el
  val inst1 : t -> I.t -> el

  val make1 : (atom -> el) -> t
end

module M (X : Sort.S with type 'a m = 'a) : S with type el = X.t =
struct
  type el = X.t
  type 'a m = 'a
  type t = X.t abs

  let len abs = Bwd.length abs.atoms

  let rec inst_atoms xs rs phi =
    match xs, rs with
    | Emp, Emp -> phi
    | Snoc (xs, x), Snoc (rs, r) ->
      inst_atoms xs rs @@
      I.cmp phi @@ I.subst r x
    | _ -> failwith "inst_atoms"

  let rec swap_atoms xs ys phi =
    match xs, ys with
    | Emp, Emp -> phi
    | Snoc (xs, x), Snoc (ys, y) ->
      swap_atoms xs ys @@
      I.cmp phi @@ I.swap y x
    | _ -> failwith "inst_atoms"

  let inst abs rs =
    let phi = inst_atoms abs.atoms rs I.idn in
    X.act phi abs.node

  let bind atoms node =
    let rec go ys atoms phi =
      match atoms with
      | Emp ->
        {atoms = Bwd.from_list ys; node = X.act phi node}
      | Snoc (atoms, x) ->
        let y = Name.named @@ Name.name x in
        go (y :: ys) atoms @@ I.cmp (I.swap x y) phi
    in
    go [] atoms I.idn

  let unleash abs =
    let xs = Bwd.map (fun x -> Name.named @@ Name.name x) abs.atoms in
    xs, inst abs @@ Bwd.map (fun x -> `Atom x) xs


  let unsafe_bind atoms node =
    bind atoms node

  let bind1 x el =
    bind (Emp #< x) el

  let unsafe_bind1 x el =
    bind1 x el

  let unsafe_map f abs =
    {abs with node = f abs.node}


  let unleash1 abs =
    let xs, el = unleash abs in
    match xs with
    | Snoc (Emp, x) -> x, el
    | _ ->
      Printexc.print_raw_backtrace stderr (Printexc.get_callstack 20);
      Format.eprintf "@.";
      failwith "unleash1: incorrect binding depth"

  let inst1 el r =
    inst el @@ Emp #< r

  let make1 gen =
    let x = Name.fresh () in
    unsafe_bind1 x (gen x)

  let act phi abs =
    let xs, node = unleash abs in
    bind xs @@ X.act phi node
end

