type 'a t = 'a option

let map f m =
  match m with
  | Some a -> Some (f a)
  | None -> None

let foreach m f = map f m

let rec filter_map f =
  function
  | [] -> []
  | (x :: xs) ->
    match f x with
    | Some y -> y :: filter_map f xs
    | None -> filter_map f xs

exception WasNone

let get_exn m =
  match m with
  | Some x -> x
  | None ->
    Printexc.print_raw_backtrace stderr (Printexc.get_callstack 20);
    Format.eprintf "@.";
    raise WasNone
