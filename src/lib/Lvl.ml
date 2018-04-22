type t = Omega | Const of int

let greater l0 l1 =
  match l0, l1 with
  | Omega, Const _ -> true
  | Const i0, Const i1 -> i0 > i1
  | _ -> false

let to_string l = 
  match l with
  | Omega -> "omega"
  | Const i -> string_of_int i