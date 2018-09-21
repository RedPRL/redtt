let counter = ref 0
let names = Hashtbl.create 1000

type t = int

let named nm =
  let i = !counter in
  counter := i + 1;
  Hashtbl.add names i nm;
  i

let fresh () =
  named None

let compare =
  Pervasives.compare

let name i =
  match Hashtbl.find names i with
  | Some x -> Some x
  | None -> None

let to_string i =
  match Hashtbl.find names i with
  | Some x -> x
  | None -> "_" ^ string_of_int i

let pp fmt i =
  Uuseg_string.pp_utf_8 fmt (to_string i)
