type 'a zip

val init : 'a -> 'a zip
val cursor : 'a zip -> 'a

type move = [`Down | `Up | `Left | `Right]

val move : move -> 'a zip -> 'a zip

(* Inserts a new node into the children of the current node. Does not move focus.
   To focus the new node, go 'down'. *)
val insert : 'a -> 'a zip -> 'a zip