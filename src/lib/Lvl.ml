type t = Omega | Const of int

let greater l0 l1 =
  match l0, l1 with
  | Omega, Const _ -> true
  | Const i0, Const i1 -> i0 > i1
  | _ -> false

let lte l0 l1 = l0 = l1 or greater l1 l0

let shift k =
  function
  | Omega -> Omega
  | Const i -> Const (i + k)

let to_string l =
  match l with
  | Omega -> "omega"
  | Const i -> string_of_int i

let pp fmt l =
  match l with
  | Omega ->
    Format.fprintf fmt "omega"
  | Const i ->
    Format.fprintf fmt "%i" i
