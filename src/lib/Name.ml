type t =
  | Const of string
  | Symbol of Symbol.t

let const str = Const str
let fresh () = Symbol (Symbol.fresh ())

let symbol =
  function
  | Const _ -> failwith "symbol"
  | Symbol sym -> sym

let pp fmt =
  function
  | Const str ->
    Uuseg_string.pp_utf_8 fmt str
  | Symbol sym ->
    Uuseg_string.pp_utf_8 fmt @@
    Symbol.to_string sym
