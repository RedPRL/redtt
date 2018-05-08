module E = ElabMonad
module Notation = Monad.Notation (E)
open Notation

module Tac = ElabTactic

let rec compile : type a. a ElabTm.t -> _ =
  fun etm ->
    match ElabTm.out etm with
    | ElabTm.Pi tele ->
      let rec go tele =
        match tele with
        | ElabTm.TEnd {cod} ->
          compile cod

        | ElabTm.TCons {vars; dom; cod} ->
          go_vars vars dom >>
          go cod

      and go_vars vars dom =
        match vars with
        | [] ->
          E.ret ()

        | x::xs ->
          Tac.Pi.formation (Some x) >>
          Tac.under begin
            compile dom >>
            E.move0 `Left >>
            go_vars xs dom
          end

      in
      go tele

    | _ ->
      failwith "TODO"
