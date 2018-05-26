open RedBasis
open Contextual
open Dev

module Notation = Monad.Notation (Contextual)
open Notation


let rec flex_term deps q =
  match Tm.unleash q.tm0 with
  | Tm.Up (Tm.Cut (Ref alpha, _)) ->
    List.map snd <@> ask >>= fun gm ->
    popl >>= fun e ->
    begin
      match e with
      | E (beta, ty, Hole) ->
        if alpha = beta then
          (* If alpha mentioned in deps, then:

              pushls (e :: deps) >>
              block (Unify q)

             else:

              pushls deps >>
                invert, blah blah
          *)
          failwith ""
        else
          (* if beta is mentiond in gm, deps or q :

               flex_term (e :: deps) q

             else:

               pushr e >>
               flex_term deps q
          *)
          failwith ""

      | _ ->
        pushr e >>
        flex_term deps q
    end
  | _ -> failwith "flex_term"
