module type S =
sig
  val find : Symbol.t -> Tm.chk Tm.t option
end

type t =
  | Proxy of (module S)

let make m =
  Proxy m

module Empty =
struct
  let find _ = failwith "Empty"
end

let empty =
  Proxy (module Empty : S)

let find x (Proxy (module M : S)) =
  M.find x
