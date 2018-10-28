type t = [`Omega | `Const of int]

let greater l0 l1 =
  match l0, l1 with
  | `Omega, _ -> true
  (* The above is wrong, but it lets us work around some annoying complications with defining large eliminations;
     it's harmless, because the user is not able to type in the Omega universe. *)

  | `Const i0, `Const i1 -> i0 > i1
  | _ -> false

let max l0 l1 =
  match l0, l1 with
  | `Const i0, `Const i1 -> `Const (max i0 i1)
  | _ -> `Omega

let lte l0 l1 = l0 = l1 || greater l1 l0

let shift k =
  function
  | `Omega -> `Omega
  | `Const i -> `Const (i + k)

let pp fmt l =
  match l with
  | `Omega ->
    Uuseg_string.pp_utf_8 fmt "ω"
  | `Const i ->
    Format.fprintf fmt "%i" i
