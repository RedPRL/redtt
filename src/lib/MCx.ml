type meta = Symbol.t
module M = Map.Make (Symbol)

type cell = 
  | Ret of Tm.chk Tm.t
  | Ask

type sequent = {lcx : LCx.t; ty : Val.can Val.t; cell : cell}

type t = sequent M.t


let emp = M.empty
let ext x seq cx = 
  M.add x seq cx

let set x tm cx = 
  match M.find_opt x cx with
  | None -> 
    failwith "MCx.set: cell does not exist"
  | Some seq ->
    match seq.cell with
    | Ask -> 
      M.add x {seq with cell = Ret tm} cx
    | Ret _ -> 
      failwith "MCx.set: cell is already set"

let lookup_exn x cx = 
  M.find x cx
