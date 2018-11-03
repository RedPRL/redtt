type id = string
type path = id list

type visibilitiy = [`Public | `Private]
type imported = [`Imported | `Skipped]

type action =
  | Star
  | Id of id
  | Replace of path * path
  | Negate of action
  | Tag of visibilitiy * action
  | Some of action list
  | All of action list
  | Seq of action * action
  | Concat of action * action
  | Saturate of action

exception InvalidAction

val compile :
  action ->
  path ->
  subpattern:bool ->
  [`Matched of (path * visibilitiy option * imported) list | `Err of string | `NoMatch]

val wrap :
  default : visibilitiy ->
  [`Matched of (path * visibilitiy option * imported) list | `Err of string | `NoMatch] ->
  (path * visibilitiy option * imported) list
