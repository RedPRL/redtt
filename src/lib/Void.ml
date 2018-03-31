type t = In of t

let rec abort (In t) = abort t