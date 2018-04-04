type 'a t = 
  { fam : DimVal.t -> 'a
  ; cache : (DimVal.t, 'a) Hashtbl.t 
  }

let inst f i = 
  match Hashtbl.find_opt f.cache i with
  | Some a -> a
  | None ->
    let a = f.fam i in
    Hashtbl.add f.cache i a;
    a

let make f = {fam = f; cache = Hashtbl.create 10}

let map f g = make @@ fun x -> f (inst g x)
let split f = 
  (make @@ fun x -> fst @@ inst f x),
  (make @@ fun x -> snd @@ inst f x)
