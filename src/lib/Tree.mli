(** A rose tree zipper. *)
type 'a zip

val init : 'a -> 'a zip
val cursor : 'a zip -> 'a


type move0 = [`Down | `Up | `Left | `Right]
type move = [`Id of move0 | `Star of move0]
exception InvalidMove of move0

(** May raise [InvalidMove]. *)
val move : move -> 'a zip -> 'a zip

(** Inserts a new node into the children of the current node. Does not move focus.
    To focus the new node, go 'down'. *)
val insert : 'a -> 'a zip -> 'a zip
