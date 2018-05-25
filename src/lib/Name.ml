let counter = ref 0
let names = Hashtbl.create 1000

type t =
  | Gen of int
  | Const of string

let const str =
  Const str

let named nm =
  let i = !counter in
  counter := i + 1;
  Hashtbl.add names i nm;
  Gen i

let fresh () =
  named None

let compare =
  Pervasives.compare

let to_string nm =
  match nm with
  | Const s ->
    s
  | Gen i ->
    match Hashtbl.find names i with
    | Some x -> x
    | None -> "%" ^ string_of_int i

let pp fmt =
  function
  | Const x ->
    Uuseg_string.pp_utf_8 fmt x
  | Gen i ->
    match Hashtbl.find names i with
    | Some x ->
      Uuseg_string.pp_utf_8 fmt x
    | None ->
      Format.fprintf fmt "%s%i" "%" i
