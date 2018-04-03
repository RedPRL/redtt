type 'a t = 'a option

let map f m = 
  match m with
  | Some a -> Some (f a)
  | None -> None