type 'a t = 'a option

let map f m =
  match m with
  | Some a -> Some (f a)
  | None -> None

exception WasNone

let get_exn m =
  match m with
  | Some x -> x
  | None -> raise WasNone
