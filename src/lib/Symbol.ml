let counter = ref 0

type t = int

let fresh () =
  let i = !counter in
  counter := i + 1;
  i