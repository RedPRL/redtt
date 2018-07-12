open RedBasis.Bwd
open BwdNotation

type atom = Name.t
type 'a abs = {atoms : atom bwd; node : 'a}

module type S =
sig
  type el

  include Sort.S with type 'a m = 'a with type t = el abs

  val bind : atom bwd -> el -> t
  val unleash : t -> atom bwd * el
  val inst : t -> I.t bwd -> el

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

  let rec freshen_atoms xs acc phi =
    match xs with
    | Emp -> Bwd.rev acc, phi
    | Snoc (xs, x) ->
      let y = Name.named @@ Name.name x in
      freshen_atoms xs (Snoc (acc, y)) @@
      I.cmp (I.swap y x) phi

  let unleash abs =
    let xs, phi = freshen_atoms abs.atoms Emp I.idn in
    xs, X.act phi abs.node

  let rec inst_atoms xs rs phi =
    match xs, rs with
    | Emp, Emp -> phi
    | Snoc (xs, x), Snoc (rs, r) ->
      inst_atoms xs rs @@
      I.cmp phi @@ I.subst r x
    | _ -> failwith "inst_atoms"

  let inst abs rs =
    let phi = inst_atoms abs.atoms rs I.idn in
    X.act phi abs.node

  (* FYI: It may not be necessary to freshen here, depending on how substitution is implemented. *)
  let bind atoms node =
    {atoms; node}
  (* let xs, phi = freshen_atoms atoms [] D.idn in
     {atoms = xs; node = X.act phi node} *)

  let bind1 x el =
    bind (Emp #< x) el

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
    bind1 x (gen x)

  let act phi abs =
    let xs, node = unleash abs in
    bind xs @@ X.act phi node
end

