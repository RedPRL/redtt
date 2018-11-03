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

exception CanFavoniaHelpMe
let compile _ = raise CanFavoniaHelpMe
let wrap ~default = raise CanFavoniaHelpMe
