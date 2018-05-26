open RedBasis
open Contextual
open Dev

module Notation = Monad.Notation (Contextual)
open Notation


let rec flex_term deps q =
  match Tm.unleash q.tm0 with
  | Tm.Up (Tm.Cut (Meta alpha, _)) ->
    List.map snd <@> ask >>= fun gm ->
    popl >>= fun e ->
    begin
      match e with
      | E (beta, ty, Hole) ->
        if alpha = beta then
          if Occurs.Set.mem alpha @@ Entries.free `Metas deps then
            pushls (e :: deps) >>
            block (Unify q)
          else
            (*
                pushls deps >>
                  invert, blah blah
            *)
            failwith "TODO"
        else
        if Occurs.Set.mem beta (Params.free `Metas gm)
        || Occurs.Set.mem beta (Entries.free `Metas deps)
        || Occurs.Set.mem beta (Equation.free `Metas q)
        then
          flex_term (e :: deps) q
        else
          pushr e >>
          flex_term deps q
      | _ ->
        pushr e >>
        flex_term deps q
    end
  | _ -> failwith "flex_term"
